// The functions of `src/rsa_oaep.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_oaep_decrypt:
	stdu %r1, -256(%r1)
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
	ld %r14, 456(%r12)
	or %r15, %r7, %r7
	or %r16, %r3, %r3
	or %r17, %r5, %r5
	ld %r18, 424(%r12)
	ld %r19, 432(%r12)
	stdu %r1, -192(%r1)
	addi %r12, %r1, 0
	std %r10, 96(%r12)
	ld %r0, 544(%r12)
	std %r0, 104(%r12)
	ld %r0, 552(%r12)
	std %r0, 112(%r12)
	ld %r0, 560(%r12)
	std %r0, 120(%r12)
	ld %r0, 568(%r12)
	std %r0, 128(%r12)
	ld %r0, 576(%r12)
	std %r0, 136(%r12)
	ld %r0, 584(%r12)
	std %r0, 144(%r12)
	ld %r0, 592(%r12)
	std %r0, 152(%r12)
	ld %r0, 600(%r12)
	std %r0, 160(%r12)
	ld %r0, 608(%r12)
	std %r0, 168(%r12)
	li %r0, 8192
	add %r0, %r14, %r0
	std %r0, 176(%r12)
	ld %r11, 656(%r12)
	addi %r11, %r11, -1024
	std %r11, 184(%r12)
	addi %r3, %r14, 0
	or %r4, %r15, %r15
	or %r5, %r6, %r6
	or %r6, %r15, %r15
	or %r7, %r8, %r8
	or %r8, %r9, %r9
	ld %r9, 632(%r12)
	or %r10, %r15, %r15
	bl {vg_rsa_private_checked}
	addi %r1, %r1, 192
	rlwinm %r20, %r3, 0, 0, 31
	addi %r3, %r1, 0
	ld %r3, 472(%r3)
	ld %r3, 32(%r3)
	addi %r4, %r3, -20
	cmpldi %cr0, %r4, 0
	beq %cr0, 20f
	addi %r4, %r3, -28
	cmpldi %cr0, %r4, 0
	beq %cr0, 22f
	addi %r4, %r3, -32
	cmpldi %cr0, %r4, 0
	beq %cr0, 24f
	addi %r4, %r3, -48
	cmpldi %cr0, %r4, 0
	beq %cr0, 26f
	li %r3, 130
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 28f
	addi %r24, %r14, 65
	addi %r25, %r15, -65
	addi %r26, %r14, 1
	li %r27, 64
	li %r28, 0
	li %r29, 0
210:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
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
	ld %r12, 480(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 480(%r9)
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
211:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 211b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 210b
	addi %r24, %r14, 1
	li %r25, 64
	addi %r26, %r14, 65
	addi %r27, %r15, -65
	li %r28, 0
	li %r29, 0
212:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
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
	ld %r12, 480(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 480(%r9)
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
213:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 213b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 212b
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r18, %r18
	or %r6, %r19, %r19
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	or %r4, %r19, %r19
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 65
	addi %r5, %r14, 1280
	lbz %r24, 0(%r14)
	li %r6, 64
214:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 214b
	addi %r4, %r14, 129
	addi %r5, %r15, -129
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r25, 0
215:
	lbz %r10, 0(%r4)
	addi %r8, %r10, -1
	rldicl %r8, %r8, 1, 63
	li %r9, 1
	xor %r9, %r10, %r9
	addi %r9, %r9, -1
	rldicl %r9, %r9, 1, 63
	or %r8, %r8, %r9
	addi %r8, %r8, -1
	and %r8, %r8, %r7
	or %r24, %r24, %r8
	li %r3, 0
	subf %r3, %r9, %r3
	and %r8, %r6, %r7
	and %r8, %r8, %r3
	or %r25, %r25, %r8
	addi %r9, %r9, -1
	and %r7, %r7, %r9
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
	or %r24, %r24, %r7
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
216:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 216b
	addi %r4, %r14, 129
	addi %r5, %r15, -129
	or %r6, %r5, %r5
	addi %r5, %r14, 2560
217:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 217b
	addi %r8, %r25, 1
	li %r9, 1
	li %r10, 10
218:
	addi %r4, %r14, 2560
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r15, %r15
219:
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
	bne %cr0, 219b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 218b
	li %r4, 1
	xor %r4, %r20, %r4
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r24, %r5
	or %r5, %r5, %r24
	rldicl %r5, %r5, 1, 63
	li %r6, 1
	xor %r5, %r5, %r6
	and %r4, %r4, %r5
	li %r26, 0
	subf %r26, %r4, %r26
	addi %r4, %r14, 2560
	or %r5, %r16, %r16
	or %r6, %r15, %r15
220:
	lbz %r7, 0(%r4)
	and %r7, %r7, %r26
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 220b
	addi %r4, %r15, -130
	subf %r4, %r25, %r4
	and %r4, %r4, %r26
	std %r4, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
	li %r4, 1
	and %r4, %r26, %r4
	or %r3, %r3, %r4
	b 29f
28:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
221:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 221b
	std %r6, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
29:
	b 27f
26:
	li %r3, 98
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 222f
	addi %r24, %r14, 49
	addi %r25, %r15, -49
	addi %r26, %r14, 1
	li %r27, 48
	li %r28, 0
	li %r29, 0
224:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
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
	ld %r12, 480(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 480(%r9)
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
225:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 225b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 224b
	addi %r24, %r14, 1
	li %r25, 48
	addi %r26, %r14, 49
	addi %r27, %r15, -49
	li %r28, 0
	li %r29, 0
226:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
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
	ld %r12, 480(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 480(%r9)
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
227:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 227b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 226b
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r18, %r18
	or %r6, %r19, %r19
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	or %r4, %r19, %r19
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 49
	addi %r5, %r14, 1280
	lbz %r24, 0(%r14)
	li %r6, 48
228:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 228b
	addi %r4, %r14, 97
	addi %r5, %r15, -97
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r25, 0
229:
	lbz %r10, 0(%r4)
	addi %r8, %r10, -1
	rldicl %r8, %r8, 1, 63
	li %r9, 1
	xor %r9, %r10, %r9
	addi %r9, %r9, -1
	rldicl %r9, %r9, 1, 63
	or %r8, %r8, %r9
	addi %r8, %r8, -1
	and %r8, %r8, %r7
	or %r24, %r24, %r8
	li %r3, 0
	subf %r3, %r9, %r3
	and %r8, %r6, %r7
	and %r8, %r8, %r3
	or %r25, %r25, %r8
	addi %r9, %r9, -1
	and %r7, %r7, %r9
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 229b
	or %r24, %r24, %r7
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
230:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 230b
	addi %r4, %r14, 97
	addi %r5, %r15, -97
	or %r6, %r5, %r5
	addi %r5, %r14, 2560
231:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 231b
	addi %r8, %r25, 1
	li %r9, 1
	li %r10, 10
232:
	addi %r4, %r14, 2560
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r15, %r15
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
	li %r4, 1
	xor %r4, %r20, %r4
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r24, %r5
	or %r5, %r5, %r24
	rldicl %r5, %r5, 1, 63
	li %r6, 1
	xor %r5, %r5, %r6
	and %r4, %r4, %r5
	li %r26, 0
	subf %r26, %r4, %r26
	addi %r4, %r14, 2560
	or %r5, %r16, %r16
	or %r6, %r15, %r15
234:
	lbz %r7, 0(%r4)
	and %r7, %r7, %r26
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 234b
	addi %r4, %r15, -98
	subf %r4, %r25, %r4
	and %r4, %r4, %r26
	std %r4, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
	li %r4, 1
	and %r4, %r26, %r4
	or %r3, %r3, %r4
	b 223f
222:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
235:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 235b
	std %r6, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
223:
27:
	b 25f
24:
	li %r3, 66
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 236f
	addi %r24, %r14, 33
	addi %r25, %r15, -33
	addi %r26, %r14, 1
	li %r27, 32
	li %r28, 0
	li %r29, 0
238:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
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
	ld %r12, 480(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 480(%r9)
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
239:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 239b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 238b
	addi %r24, %r14, 1
	li %r25, 32
	addi %r26, %r14, 33
	addi %r27, %r15, -33
	li %r28, 0
	li %r29, 0
240:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
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
	ld %r12, 480(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 480(%r9)
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
241:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 241b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 240b
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r18, %r18
	or %r6, %r19, %r19
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	or %r4, %r19, %r19
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 33
	addi %r5, %r14, 1280
	lbz %r24, 0(%r14)
	li %r6, 32
242:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 242b
	addi %r4, %r14, 65
	addi %r5, %r15, -65
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r25, 0
243:
	lbz %r10, 0(%r4)
	addi %r8, %r10, -1
	rldicl %r8, %r8, 1, 63
	li %r9, 1
	xor %r9, %r10, %r9
	addi %r9, %r9, -1
	rldicl %r9, %r9, 1, 63
	or %r8, %r8, %r9
	addi %r8, %r8, -1
	and %r8, %r8, %r7
	or %r24, %r24, %r8
	li %r3, 0
	subf %r3, %r9, %r3
	and %r8, %r6, %r7
	and %r8, %r8, %r3
	or %r25, %r25, %r8
	addi %r9, %r9, -1
	and %r7, %r7, %r9
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 243b
	or %r24, %r24, %r7
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
244:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 244b
	addi %r4, %r14, 65
	addi %r5, %r15, -65
	or %r6, %r5, %r5
	addi %r5, %r14, 2560
245:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 245b
	addi %r8, %r25, 1
	li %r9, 1
	li %r10, 10
246:
	addi %r4, %r14, 2560
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r15, %r15
247:
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
	bne %cr0, 247b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 246b
	li %r4, 1
	xor %r4, %r20, %r4
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r24, %r5
	or %r5, %r5, %r24
	rldicl %r5, %r5, 1, 63
	li %r6, 1
	xor %r5, %r5, %r6
	and %r4, %r4, %r5
	li %r26, 0
	subf %r26, %r4, %r26
	addi %r4, %r14, 2560
	or %r5, %r16, %r16
	or %r6, %r15, %r15
248:
	lbz %r7, 0(%r4)
	and %r7, %r7, %r26
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 248b
	addi %r4, %r15, -66
	subf %r4, %r25, %r4
	and %r4, %r4, %r26
	std %r4, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
	li %r4, 1
	and %r4, %r26, %r4
	or %r3, %r3, %r4
	b 237f
236:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
249:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 249b
	std %r6, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
237:
25:
	b 23f
22:
	li %r3, 58
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 250f
	addi %r24, %r14, 29
	addi %r25, %r15, -29
	addi %r26, %r14, 1
	li %r27, 28
	li %r28, 0
	li %r29, 0
252:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
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
	ld %r12, 480(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 480(%r9)
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
253:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 253b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 252b
	addi %r24, %r14, 1
	li %r25, 28
	addi %r26, %r14, 29
	addi %r27, %r15, -29
	li %r28, 0
	li %r29, 0
254:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
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
	ld %r12, 480(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 480(%r9)
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
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 254b
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r18, %r18
	or %r6, %r19, %r19
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	or %r4, %r19, %r19
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 29
	addi %r5, %r14, 1280
	lbz %r24, 0(%r14)
	li %r6, 28
256:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 256b
	addi %r4, %r14, 57
	addi %r5, %r15, -57
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r25, 0
257:
	lbz %r10, 0(%r4)
	addi %r8, %r10, -1
	rldicl %r8, %r8, 1, 63
	li %r9, 1
	xor %r9, %r10, %r9
	addi %r9, %r9, -1
	rldicl %r9, %r9, 1, 63
	or %r8, %r8, %r9
	addi %r8, %r8, -1
	and %r8, %r8, %r7
	or %r24, %r24, %r8
	li %r3, 0
	subf %r3, %r9, %r3
	and %r8, %r6, %r7
	and %r8, %r8, %r3
	or %r25, %r25, %r8
	addi %r9, %r9, -1
	and %r7, %r7, %r9
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 257b
	or %r24, %r24, %r7
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
258:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 258b
	addi %r4, %r14, 57
	addi %r5, %r15, -57
	or %r6, %r5, %r5
	addi %r5, %r14, 2560
259:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 259b
	addi %r8, %r25, 1
	li %r9, 1
	li %r10, 10
260:
	addi %r4, %r14, 2560
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r15, %r15
261:
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
	bne %cr0, 261b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 260b
	li %r4, 1
	xor %r4, %r20, %r4
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r24, %r5
	or %r5, %r5, %r24
	rldicl %r5, %r5, 1, 63
	li %r6, 1
	xor %r5, %r5, %r6
	and %r4, %r4, %r5
	li %r26, 0
	subf %r26, %r4, %r26
	addi %r4, %r14, 2560
	or %r5, %r16, %r16
	or %r6, %r15, %r15
262:
	lbz %r7, 0(%r4)
	and %r7, %r7, %r26
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 262b
	addi %r4, %r15, -58
	subf %r4, %r25, %r4
	and %r4, %r4, %r26
	std %r4, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
	li %r4, 1
	and %r4, %r26, %r4
	or %r3, %r3, %r4
	b 251f
250:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
263:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 263b
	std %r6, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
251:
23:
	b 21f
20:
	li %r3, 42
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 264f
	addi %r24, %r14, 21
	addi %r25, %r15, -21
	addi %r26, %r14, 1
	li %r27, 20
	li %r28, 0
	li %r29, 0
266:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
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
	ld %r12, 480(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 480(%r9)
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
267:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 267b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 266b
	addi %r24, %r14, 1
	li %r25, 20
	addi %r26, %r14, 21
	addi %r27, %r15, -21
	li %r28, 0
	li %r29, 0
268:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
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
	ld %r12, 480(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 480(%r9)
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
269:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 269b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 268b
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r18, %r18
	or %r6, %r19, %r19
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	or %r4, %r19, %r19
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 472(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 21
	addi %r5, %r14, 1280
	lbz %r24, 0(%r14)
	li %r6, 20
270:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 270b
	addi %r4, %r14, 41
	addi %r5, %r15, -41
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r25, 0
271:
	lbz %r10, 0(%r4)
	addi %r8, %r10, -1
	rldicl %r8, %r8, 1, 63
	li %r9, 1
	xor %r9, %r10, %r9
	addi %r9, %r9, -1
	rldicl %r9, %r9, 1, 63
	or %r8, %r8, %r9
	addi %r8, %r8, -1
	and %r8, %r8, %r7
	or %r24, %r24, %r8
	li %r3, 0
	subf %r3, %r9, %r3
	and %r8, %r6, %r7
	and %r8, %r8, %r3
	or %r25, %r25, %r8
	addi %r9, %r9, -1
	and %r7, %r7, %r9
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 271b
	or %r24, %r24, %r7
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
272:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 272b
	addi %r4, %r14, 41
	addi %r5, %r15, -41
	or %r6, %r5, %r5
	addi %r5, %r14, 2560
273:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 273b
	addi %r8, %r25, 1
	li %r9, 1
	li %r10, 10
274:
	addi %r4, %r14, 2560
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r15, %r15
275:
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
	bne %cr0, 275b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 274b
	li %r4, 1
	xor %r4, %r20, %r4
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r24, %r5
	or %r5, %r5, %r24
	rldicl %r5, %r5, 1, 63
	li %r6, 1
	xor %r5, %r5, %r6
	and %r4, %r4, %r5
	li %r26, 0
	subf %r26, %r4, %r26
	addi %r4, %r14, 2560
	or %r5, %r16, %r16
	or %r6, %r15, %r15
276:
	lbz %r7, 0(%r4)
	and %r7, %r7, %r26
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 276b
	addi %r4, %r15, -42
	subf %r4, %r25, %r4
	and %r4, %r4, %r26
	std %r4, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
	li %r4, 1
	and %r4, %r26, %r4
	or %r3, %r3, %r4
	b 265f
264:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
277:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 277b
	std %r6, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
265:
21:
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
	addi %r1, %r1, 256
	blr

vg_rsa_oaep_encrypt_precomputed:
	stdu %r1, -256(%r1)
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
	ld %r14, 384(%r12)
	or %r15, %r6, %r6
	or %r16, %r3, %r3
	or %r17, %r7, %r7
	or %r18, %r8, %r8
	or %r19, %r9, %r9
	or %r20, %r10, %r10
	ld %r21, 400(%r12)
	ld %r22, 408(%r12)
	ld %r23, 392(%r12)
	ld %r9, 352(%r12)
	ld %r10, 360(%r12)
	ld %r11, 368(%r12)
	addi %r3, %r1, 0
	ld %r3, 416(%r3)
	ld %r3, 32(%r3)
	addi %r4, %r3, -20
	cmpldi %cr0, %r4, 0
	beq %cr0, 20f
	addi %r4, %r3, -28
	cmpldi %cr0, %r4, 0
	beq %cr0, 22f
	addi %r4, %r3, -32
	cmpldi %cr0, %r4, 0
	beq %cr0, 24f
	addi %r4, %r3, -48
	cmpldi %cr0, %r4, 0
	beq %cr0, 26f
	li %r3, 130
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 28f
	li %r3, 130
	subf %r4, %r3, %r15
	subf %r4, %r10, %r4
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r10, 1, 63
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 210f
	addi %r4, %r14, 0
	li %r5, 1024
	li %r6, 0
212:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 212b
	or %r4, %r11, %r11
	addi %r5, %r14, 1
	li %r6, 64
213:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 213b
	add %r5, %r14, %r15
	subf %r5, %r10, %r5
	addi %r5, %r5, -1
	li %r7, 1
	stb %r7, 0(%r5)
	addi %r5, %r5, 1
	or %r4, %r9, %r9
	or %r6, %r10, %r10
	cmpldi %cr0, %r6, 0
	bne %cr0, 214f
	b 215f
214:
216:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 216b
215:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r19, %r19
	or %r6, %r20, %r20
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	or %r4, %r20, %r20
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 1280
	addi %r5, %r14, 65
	li %r6, 64
217:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 217b
	addi %r24, %r14, 1
	li %r25, 64
	addi %r26, %r14, 65
	addi %r27, %r15, -65
	li %r28, 0
	li %r29, 0
218:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
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
	ld %r12, 424(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 424(%r9)
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
219:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 219b
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 218b
	addi %r24, %r14, 65
	addi %r25, %r15, -65
	addi %r26, %r14, 1
	li %r27, 64
	li %r28, 0
	li %r29, 0
220:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
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
	ld %r12, 424(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 424(%r9)
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
221:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 221b
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 220b
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r23, -1024
	std %r5, 104(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r21, %r21
	or %r6, %r22, %r22
	or %r7, %r17, %r17
	or %r8, %r18, %r18
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	b 211f
210:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
222:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 222b
	li %r3, 0
211:
	b 29f
28:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
223:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 223b
	li %r3, 0
29:
	b 27f
26:
	li %r3, 98
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 224f
	li %r3, 98
	subf %r4, %r3, %r15
	subf %r4, %r10, %r4
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r10, 1, 63
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 226f
	addi %r4, %r14, 0
	li %r5, 1024
	li %r6, 0
228:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 228b
	or %r4, %r11, %r11
	addi %r5, %r14, 1
	li %r6, 48
229:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 229b
	add %r5, %r14, %r15
	subf %r5, %r10, %r5
	addi %r5, %r5, -1
	li %r7, 1
	stb %r7, 0(%r5)
	addi %r5, %r5, 1
	or %r4, %r9, %r9
	or %r6, %r10, %r10
	cmpldi %cr0, %r6, 0
	bne %cr0, 230f
	b 231f
230:
232:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 232b
231:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r19, %r19
	or %r6, %r20, %r20
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	or %r4, %r20, %r20
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 1280
	addi %r5, %r14, 49
	li %r6, 48
233:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 233b
	addi %r24, %r14, 1
	li %r25, 48
	addi %r26, %r14, 49
	addi %r27, %r15, -49
	li %r28, 0
	li %r29, 0
234:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
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
	ld %r12, 424(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 424(%r9)
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
235:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 235b
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 234b
	addi %r24, %r14, 49
	addi %r25, %r15, -49
	addi %r26, %r14, 1
	li %r27, 48
	li %r28, 0
	li %r29, 0
236:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
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
	ld %r12, 424(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 424(%r9)
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
237:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 237b
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 236b
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r23, -1024
	std %r5, 104(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r21, %r21
	or %r6, %r22, %r22
	or %r7, %r17, %r17
	or %r8, %r18, %r18
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	b 227f
226:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
238:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 238b
	li %r3, 0
227:
	b 225f
224:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
239:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 239b
	li %r3, 0
225:
27:
	b 25f
24:
	li %r3, 66
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 240f
	li %r3, 66
	subf %r4, %r3, %r15
	subf %r4, %r10, %r4
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r10, 1, 63
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 242f
	addi %r4, %r14, 0
	li %r5, 1024
	li %r6, 0
244:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 244b
	or %r4, %r11, %r11
	addi %r5, %r14, 1
	li %r6, 32
245:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 245b
	add %r5, %r14, %r15
	subf %r5, %r10, %r5
	addi %r5, %r5, -1
	li %r7, 1
	stb %r7, 0(%r5)
	addi %r5, %r5, 1
	or %r4, %r9, %r9
	or %r6, %r10, %r10
	cmpldi %cr0, %r6, 0
	bne %cr0, 246f
	b 247f
246:
248:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 248b
247:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r19, %r19
	or %r6, %r20, %r20
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	or %r4, %r20, %r20
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 1280
	addi %r5, %r14, 33
	li %r6, 32
249:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 249b
	addi %r24, %r14, 1
	li %r25, 32
	addi %r26, %r14, 33
	addi %r27, %r15, -33
	li %r28, 0
	li %r29, 0
250:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
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
	ld %r12, 424(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 424(%r9)
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
251:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 251b
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 250b
	addi %r24, %r14, 33
	addi %r25, %r15, -33
	addi %r26, %r14, 1
	li %r27, 32
	li %r28, 0
	li %r29, 0
252:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
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
	ld %r12, 424(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 424(%r9)
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
253:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 253b
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 252b
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r23, -1024
	std %r5, 104(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r21, %r21
	or %r6, %r22, %r22
	or %r7, %r17, %r17
	or %r8, %r18, %r18
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	b 243f
242:
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
243:
	b 241f
240:
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
241:
25:
	b 23f
22:
	li %r3, 58
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 256f
	li %r3, 58
	subf %r4, %r3, %r15
	subf %r4, %r10, %r4
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r10, 1, 63
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 258f
	addi %r4, %r14, 0
	li %r5, 1024
	li %r6, 0
260:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 260b
	or %r4, %r11, %r11
	addi %r5, %r14, 1
	li %r6, 28
261:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 261b
	add %r5, %r14, %r15
	subf %r5, %r10, %r5
	addi %r5, %r5, -1
	li %r7, 1
	stb %r7, 0(%r5)
	addi %r5, %r5, 1
	or %r4, %r9, %r9
	or %r6, %r10, %r10
	cmpldi %cr0, %r6, 0
	bne %cr0, 262f
	b 263f
262:
264:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 264b
263:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r19, %r19
	or %r6, %r20, %r20
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	or %r4, %r20, %r20
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 1280
	addi %r5, %r14, 29
	li %r6, 28
265:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 265b
	addi %r24, %r14, 1
	li %r25, 28
	addi %r26, %r14, 29
	addi %r27, %r15, -29
	li %r28, 0
	li %r29, 0
266:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
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
	ld %r12, 424(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 424(%r9)
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
267:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 267b
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 266b
	addi %r24, %r14, 29
	addi %r25, %r15, -29
	addi %r26, %r14, 1
	li %r27, 28
	li %r28, 0
	li %r29, 0
268:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
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
	ld %r12, 424(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 424(%r9)
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
269:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 269b
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 268b
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r23, -1024
	std %r5, 104(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r21, %r21
	or %r6, %r22, %r22
	or %r7, %r17, %r17
	or %r8, %r18, %r18
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	b 259f
258:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
270:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 270b
	li %r3, 0
259:
	b 257f
256:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
271:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 271b
	li %r3, 0
257:
23:
	b 21f
20:
	li %r3, 42
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 272f
	li %r3, 42
	subf %r4, %r3, %r15
	subf %r4, %r10, %r4
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r10, 1, 63
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 274f
	addi %r4, %r14, 0
	li %r5, 1024
	li %r6, 0
276:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 276b
	or %r4, %r11, %r11
	addi %r5, %r14, 1
	li %r6, 20
277:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 277b
	add %r5, %r14, %r15
	subf %r5, %r10, %r5
	addi %r5, %r5, -1
	li %r7, 1
	stb %r7, 0(%r5)
	addi %r5, %r5, 1
	or %r4, %r9, %r9
	or %r6, %r10, %r10
	cmpldi %cr0, %r6, 0
	bne %cr0, 278f
	b 279f
278:
280:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 280b
279:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r19, %r19
	or %r6, %r20, %r20
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	or %r4, %r20, %r20
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 416(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r4, %r14, 1280
	addi %r5, %r14, 21
	li %r6, 20
281:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 281b
	addi %r24, %r14, 1
	li %r25, 20
	addi %r26, %r14, 21
	addi %r27, %r15, -21
	li %r28, 0
	li %r29, 0
282:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
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
	ld %r12, 424(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 424(%r9)
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
283:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 283b
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 282b
	addi %r24, %r14, 21
	addi %r25, %r15, -21
	addi %r26, %r14, 1
	li %r27, 20
	li %r28, 0
	li %r29, 0
284:
	addi %r3, %r14, 1024
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 0(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
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
	ld %r12, 424(%r12)
	ld %r12, 8(%r12)
	mtctr %r12
	bctrl
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 16(%r12)
	mtctr %r12
	bctrl
	addi %r9, %r1, 0
	ld %r9, 424(%r9)
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
285:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 285b
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 284b
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r23, -1024
	std %r5, 104(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r21, %r21
	or %r6, %r22, %r22
	or %r7, %r17, %r17
	or %r8, %r18, %r18
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	b 275f
274:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
286:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 286b
	li %r3, 0
275:
	b 273f
272:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
287:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 287b
	li %r3, 0
273:
21:
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
	addi %r1, %r1, 256
	blr
