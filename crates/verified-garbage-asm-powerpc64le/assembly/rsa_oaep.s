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
	addi %r4, %r3, -16
	cmpldi %cr0, %r4, 0
	beq %cr0, 20f
	addi %r4, %r3, -20
	cmpldi %cr0, %r4, 0
	beq %cr0, 22f
	addi %r4, %r3, -28
	cmpldi %cr0, %r4, 0
	beq %cr0, 24f
	addi %r4, %r3, -32
	cmpldi %cr0, %r4, 0
	beq %cr0, 26f
	addi %r4, %r3, -48
	cmpldi %cr0, %r4, 0
	beq %cr0, 28f
	li %r3, 130
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 210f
	addi %r24, %r14, 65
	addi %r25, %r15, -65
	addi %r26, %r14, 1
	li %r27, 64
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
	addi %r24, %r14, 1
	li %r25, 64
	addi %r26, %r14, 65
	addi %r27, %r15, -65
	li %r28, 0
	li %r29, 0
214:
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
215:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 215b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 214b
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
216:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 216b
	addi %r4, %r14, 129
	addi %r5, %r15, -129
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r25, 0
217:
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
	bne %cr0, 217b
	or %r24, %r24, %r7
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
218:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 218b
	addi %r4, %r14, 129
	addi %r5, %r15, -129
	or %r6, %r5, %r5
	addi %r5, %r14, 2560
219:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 219b
	addi %r8, %r25, 1
	li %r9, 1
	li %r10, 10
220:
	addi %r4, %r14, 2560
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r15, %r15
221:
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
	bne %cr0, 221b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 220b
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
222:
	lbz %r7, 0(%r4)
	and %r7, %r7, %r26
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 222b
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
	b 211f
210:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
223:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 223b
	std %r6, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
211:
	b 29f
28:
	li %r3, 98
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 224f
	addi %r24, %r14, 49
	addi %r25, %r15, -49
	addi %r26, %r14, 1
	li %r27, 48
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
	addi %r24, %r14, 1
	li %r25, 48
	addi %r26, %r14, 49
	addi %r27, %r15, -49
	li %r28, 0
	li %r29, 0
228:
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
229:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 229b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 228b
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
230:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 230b
	addi %r4, %r14, 97
	addi %r5, %r15, -97
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r25, 0
231:
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
	bne %cr0, 231b
	or %r24, %r24, %r7
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
232:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 232b
	addi %r4, %r14, 97
	addi %r5, %r15, -97
	or %r6, %r5, %r5
	addi %r5, %r14, 2560
233:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 233b
	addi %r8, %r25, 1
	li %r9, 1
	li %r10, 10
234:
	addi %r4, %r14, 2560
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r15, %r15
235:
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
	bne %cr0, 235b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 234b
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
236:
	lbz %r7, 0(%r4)
	and %r7, %r7, %r26
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 236b
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
	b 225f
224:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
237:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 237b
	std %r6, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
225:
29:
	b 27f
26:
	li %r3, 66
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 238f
	addi %r24, %r14, 33
	addi %r25, %r15, -33
	addi %r26, %r14, 1
	li %r27, 32
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
	addi %r24, %r14, 1
	li %r25, 32
	addi %r26, %r14, 33
	addi %r27, %r15, -33
	li %r28, 0
	li %r29, 0
242:
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
243:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 243b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 242b
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
244:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 244b
	addi %r4, %r14, 65
	addi %r5, %r15, -65
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r25, 0
245:
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
	bne %cr0, 245b
	or %r24, %r24, %r7
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
246:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 246b
	addi %r4, %r14, 65
	addi %r5, %r15, -65
	or %r6, %r5, %r5
	addi %r5, %r14, 2560
247:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 247b
	addi %r8, %r25, 1
	li %r9, 1
	li %r10, 10
248:
	addi %r4, %r14, 2560
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r15, %r15
249:
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
	bne %cr0, 249b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 248b
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
250:
	lbz %r7, 0(%r4)
	and %r7, %r7, %r26
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 250b
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
	b 239f
238:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
251:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 251b
	std %r6, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
239:
27:
	b 25f
24:
	li %r3, 58
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 252f
	addi %r24, %r14, 29
	addi %r25, %r15, -29
	addi %r26, %r14, 1
	li %r27, 28
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
	addi %r24, %r14, 1
	li %r25, 28
	addi %r26, %r14, 29
	addi %r27, %r15, -29
	li %r28, 0
	li %r29, 0
256:
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
257:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 257b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 256b
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
258:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 258b
	addi %r4, %r14, 57
	addi %r5, %r15, -57
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r25, 0
259:
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
	bne %cr0, 259b
	or %r24, %r24, %r7
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
260:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 260b
	addi %r4, %r14, 57
	addi %r5, %r15, -57
	or %r6, %r5, %r5
	addi %r5, %r14, 2560
261:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 261b
	addi %r8, %r25, 1
	li %r9, 1
	li %r10, 10
262:
	addi %r4, %r14, 2560
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r15, %r15
263:
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
	bne %cr0, 263b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 262b
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
264:
	lbz %r7, 0(%r4)
	and %r7, %r7, %r26
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 264b
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
	b 253f
252:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
265:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 265b
	std %r6, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
253:
25:
	b 23f
22:
	li %r3, 42
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 266f
	addi %r24, %r14, 21
	addi %r25, %r15, -21
	addi %r26, %r14, 1
	li %r27, 20
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
	addi %r24, %r14, 1
	li %r25, 20
	addi %r26, %r14, 21
	addi %r27, %r15, -21
	li %r28, 0
	li %r29, 0
270:
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
271:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 271b
	addi %r12, %r1, 0
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 270b
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
272:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 272b
	addi %r4, %r14, 41
	addi %r5, %r15, -41
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r25, 0
273:
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
	bne %cr0, 273b
	or %r24, %r24, %r7
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
274:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 274b
	addi %r4, %r14, 41
	addi %r5, %r15, -41
	or %r6, %r5, %r5
	addi %r5, %r14, 2560
275:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 275b
	addi %r8, %r25, 1
	li %r9, 1
	li %r10, 10
276:
	addi %r4, %r14, 2560
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r15, %r15
277:
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
	bne %cr0, 277b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 276b
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
278:
	lbz %r7, 0(%r4)
	and %r7, %r7, %r26
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 278b
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
	b 267f
266:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
279:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 279b
	std %r6, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
267:
23:
	b 21f
20:
	li %r3, 34
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 280f
	addi %r24, %r14, 17
	addi %r25, %r15, -17
	addi %r26, %r14, 1
	li %r27, 16
	li %r28, 0
	li %r29, 0
282:
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
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 282b
	addi %r24, %r14, 1
	li %r25, 16
	addi %r26, %r14, 17
	addi %r27, %r15, -17
	li %r28, 0
	li %r29, 0
284:
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
	ld %r12, 480(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 284b
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
	addi %r4, %r14, 17
	addi %r5, %r14, 1280
	lbz %r24, 0(%r14)
	li %r6, 16
286:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 286b
	addi %r4, %r14, 33
	addi %r5, %r15, -33
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r25, 0
287:
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
	bne %cr0, 287b
	or %r24, %r24, %r7
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
288:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 288b
	addi %r4, %r14, 33
	addi %r5, %r15, -33
	or %r6, %r5, %r5
	addi %r5, %r14, 2560
289:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 289b
	addi %r8, %r25, 1
	li %r9, 1
	li %r10, 10
290:
	addi %r4, %r14, 2560
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r15, %r15
291:
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
	bne %cr0, 291b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 290b
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
292:
	lbz %r7, 0(%r4)
	and %r7, %r7, %r26
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 292b
	addi %r4, %r15, -34
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
	b 281f
280:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
293:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 293b
	std %r6, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
281:
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
	.p2align 6

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
	addi %r4, %r3, -16
	cmpldi %cr0, %r4, 0
	beq %cr0, 20f
	addi %r4, %r3, -20
	cmpldi %cr0, %r4, 0
	beq %cr0, 22f
	addi %r4, %r3, -28
	cmpldi %cr0, %r4, 0
	beq %cr0, 24f
	addi %r4, %r3, -32
	cmpldi %cr0, %r4, 0
	beq %cr0, 26f
	addi %r4, %r3, -48
	cmpldi %cr0, %r4, 0
	beq %cr0, 28f
	li %r3, 130
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 210f
	li %r3, 130
	subf %r4, %r3, %r15
	subf %r4, %r10, %r4
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r10, 1, 63
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 212f
	addi %r4, %r14, 0
	li %r5, 1024
	li %r6, 0
214:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 214b
	or %r4, %r11, %r11
	addi %r5, %r14, 1
	li %r6, 64
215:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 215b
	add %r5, %r14, %r15
	subf %r5, %r10, %r5
	addi %r5, %r5, -1
	li %r7, 1
	stb %r7, 0(%r5)
	addi %r5, %r5, 1
	or %r4, %r9, %r9
	or %r6, %r10, %r10
	cmpldi %cr0, %r6, 0
	bne %cr0, 216f
	b 217f
216:
218:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 218b
217:
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
219:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 219b
	addi %r24, %r14, 1
	li %r25, 64
	addi %r26, %r14, 65
	addi %r27, %r15, -65
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
	addi %r24, %r14, 65
	addi %r25, %r15, -65
	addi %r26, %r14, 1
	li %r27, 64
	li %r28, 0
	li %r29, 0
222:
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
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 222b
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
	b 213f
212:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
224:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 224b
	li %r3, 0
213:
	b 211f
210:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
225:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 225b
	li %r3, 0
211:
	b 29f
28:
	li %r3, 98
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 226f
	li %r3, 98
	subf %r4, %r3, %r15
	subf %r4, %r10, %r4
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r10, 1, 63
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 228f
	addi %r4, %r14, 0
	li %r5, 1024
	li %r6, 0
230:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 230b
	or %r4, %r11, %r11
	addi %r5, %r14, 1
	li %r6, 48
231:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 231b
	add %r5, %r14, %r15
	subf %r5, %r10, %r5
	addi %r5, %r5, -1
	li %r7, 1
	stb %r7, 0(%r5)
	addi %r5, %r5, 1
	or %r4, %r9, %r9
	or %r6, %r10, %r10
	cmpldi %cr0, %r6, 0
	bne %cr0, 232f
	b 233f
232:
234:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 234b
233:
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
235:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 235b
	addi %r24, %r14, 1
	li %r25, 48
	addi %r26, %r14, 49
	addi %r27, %r15, -49
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
	addi %r24, %r14, 49
	addi %r25, %r15, -49
	addi %r26, %r14, 1
	li %r27, 48
	li %r28, 0
	li %r29, 0
238:
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
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 238b
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
	b 229f
228:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
240:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 240b
	li %r3, 0
229:
	b 227f
226:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
241:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 241b
	li %r3, 0
227:
29:
	b 27f
26:
	li %r3, 66
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 242f
	li %r3, 66
	subf %r4, %r3, %r15
	subf %r4, %r10, %r4
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r10, 1, 63
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 244f
	addi %r4, %r14, 0
	li %r5, 1024
	li %r6, 0
246:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 246b
	or %r4, %r11, %r11
	addi %r5, %r14, 1
	li %r6, 32
247:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 247b
	add %r5, %r14, %r15
	subf %r5, %r10, %r5
	addi %r5, %r5, -1
	li %r7, 1
	stb %r7, 0(%r5)
	addi %r5, %r5, 1
	or %r4, %r9, %r9
	or %r6, %r10, %r10
	cmpldi %cr0, %r6, 0
	bne %cr0, 248f
	b 249f
248:
250:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 250b
249:
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
251:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 251b
	addi %r24, %r14, 1
	li %r25, 32
	addi %r26, %r14, 33
	addi %r27, %r15, -33
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
	addi %r24, %r14, 33
	addi %r25, %r15, -33
	addi %r26, %r14, 1
	li %r27, 32
	li %r28, 0
	li %r29, 0
254:
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
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 254b
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
	b 245f
244:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
256:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 256b
	li %r3, 0
245:
	b 243f
242:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
257:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 257b
	li %r3, 0
243:
27:
	b 25f
24:
	li %r3, 58
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 258f
	li %r3, 58
	subf %r4, %r3, %r15
	subf %r4, %r10, %r4
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r10, 1, 63
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 260f
	addi %r4, %r14, 0
	li %r5, 1024
	li %r6, 0
262:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 262b
	or %r4, %r11, %r11
	addi %r5, %r14, 1
	li %r6, 28
263:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 263b
	add %r5, %r14, %r15
	subf %r5, %r10, %r5
	addi %r5, %r5, -1
	li %r7, 1
	stb %r7, 0(%r5)
	addi %r5, %r5, 1
	or %r4, %r9, %r9
	or %r6, %r10, %r10
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
267:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 267b
	addi %r24, %r14, 1
	li %r25, 28
	addi %r26, %r14, 29
	addi %r27, %r15, -29
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
	addi %r24, %r14, 29
	addi %r25, %r15, -29
	addi %r26, %r14, 1
	li %r27, 28
	li %r28, 0
	li %r29, 0
270:
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
271:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 271b
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 270b
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
	b 261f
260:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
272:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 272b
	li %r3, 0
261:
	b 259f
258:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
273:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 273b
	li %r3, 0
259:
25:
	b 23f
22:
	li %r3, 42
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 274f
	li %r3, 42
	subf %r4, %r3, %r15
	subf %r4, %r10, %r4
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r10, 1, 63
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 276f
	addi %r4, %r14, 0
	li %r5, 1024
	li %r6, 0
278:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 278b
	or %r4, %r11, %r11
	addi %r5, %r14, 1
	li %r6, 20
279:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 279b
	add %r5, %r14, %r15
	subf %r5, %r10, %r5
	addi %r5, %r5, -1
	li %r7, 1
	stb %r7, 0(%r5)
	addi %r5, %r5, 1
	or %r4, %r9, %r9
	or %r6, %r10, %r10
	cmpldi %cr0, %r6, 0
	bne %cr0, 280f
	b 281f
280:
282:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 282b
281:
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
283:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 283b
	addi %r24, %r14, 1
	li %r25, 20
	addi %r26, %r14, 21
	addi %r27, %r15, -21
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
	addi %r24, %r14, 21
	addi %r25, %r15, -21
	addi %r26, %r14, 1
	li %r27, 20
	li %r28, 0
	li %r29, 0
286:
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
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 286b
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
	b 277f
276:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
288:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 288b
	li %r3, 0
277:
	b 275f
274:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
289:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 289b
	li %r3, 0
275:
23:
	b 21f
20:
	li %r3, 34
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 290f
	li %r3, 34
	subf %r4, %r3, %r15
	subf %r4, %r10, %r4
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r10, 1, 63
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 292f
	addi %r4, %r14, 0
	li %r5, 1024
	li %r6, 0
294:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 294b
	or %r4, %r11, %r11
	addi %r5, %r14, 1
	li %r6, 16
295:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 295b
	add %r5, %r14, %r15
	subf %r5, %r10, %r5
	addi %r5, %r5, -1
	li %r7, 1
	stb %r7, 0(%r5)
	addi %r5, %r5, 1
	or %r4, %r9, %r9
	or %r6, %r10, %r10
	cmpldi %cr0, %r6, 0
	bne %cr0, 296f
	b 297f
296:
298:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 298b
297:
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
	addi %r5, %r14, 17
	li %r6, 16
299:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 299b
	addi %r24, %r14, 1
	li %r25, 16
	addi %r26, %r14, 17
	addi %r27, %r15, -17
	li %r28, 0
	li %r29, 0
2100:
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
2101:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2101b
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 2100b
	addi %r24, %r14, 17
	addi %r25, %r15, -17
	addi %r26, %r14, 1
	li %r27, 16
	li %r28, 0
	li %r29, 0
2102:
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
2103:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2103b
	addi %r12, %r1, 0
	ld %r12, 424(%r12)
	ld %r12, 32(%r12)
	addi %r28, %r28, 1
	add %r29, %r29, %r12
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 2102b
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
	b 293f
292:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2104:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2104b
	li %r3, 0
293:
	b 291f
290:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
2105:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2105b
	li %r3, 0
291:
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
	.p2align 6
