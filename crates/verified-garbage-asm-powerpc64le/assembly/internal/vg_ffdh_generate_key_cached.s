// The functions of `src/internal/vg_ffdh_generate_key_cached.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_generate_key_cached:
	addi %r11, %r1, 104
	ld %r11, 0(%r11)
	addi %r12, %r1, 120
	ld %r12, 0(%r12)
	std %r14, 112(%r11)
	std %r15, 120(%r11)
	std %r16, 128(%r11)
	std %r17, 136(%r11)
	std %r18, 144(%r11)
	std %r19, 152(%r11)
	std %r20, 160(%r11)
	std %r21, 168(%r11)
	std %r22, 176(%r11)
	std %r24, 184(%r11)
	std %r25, 192(%r11)
	std %r26, 200(%r11)
	std %r27, 208(%r11)
	std %r28, 216(%r11)
	std %r29, 224(%r11)
	std %r30, 232(%r11)
	std %r31, 240(%r11)
	std %r23, 248(%r11)
	addi %r23, %r11, 0
	ld %r0, 0(%r12)
	ld %r6, 8(%r12)
	ld %r11, 16(%r12)
	std %r12, 0(%r23)
	std %r0, 8(%r23)
	std %r6, 16(%r23)
	std %r11, 24(%r23)
	std %r3, 64(%r23)
	std %r4, 72(%r23)
	std %r5, 80(%r23)
	std %r10, 88(%r23)
	addi %r3, %r7, 0
	addi %r4, %r8, 0
	addi %r5, %r9, 0
	addi %r21, %r3, 0
	addi %r27, %r4, 0
	addi %r28, %r5, 0
	addi %r11, %r5, 7
	rldicl %r11, %r11, 61, 3
	rldicr %r29, %r11, 3, 60
	addi %r29, %r29, 16
	addi %r10, %r23, 256
	rldicr %r11, %r11, 1, 62
	addi %r31, %r23, 0
	addi %r12, %r21, 0
	addi %r6, %r28, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
20:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
21:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 21b
	add %r15, %r12, %r6
	addi %r15, %r15, -1
	lbz %r0, 0(%r15)
	li %r18, 1
	and %r0, %r0, %r18
	xor %r0, %r0, %r18
	lbz %r15, 0(%r12)
	cmpldi %cr0, %r15, 0
	beq %cr0, 22f
	b 23f
22:
	li %r0, 1
23:
	addi %r16, %r6, -64
	cmpldi %cr0, %r16, 0
	beq %cr0, 24f
	b 25f
24:
	rldicl %r15, %r15, 57, 7
	xor %r15, %r15, %r18
	or %r0, %r0, %r15
25:
	cmpldi %cr0, %r0, 0
	beq %cr0, 26f
	li %r3, 0
	b 27f
26:
	ld %r17, 16(%r23)
	rldicr %r17, %r17, 3, 60
	ld %r18, 8(%r23)
	subf %r17, %r18, %r17
	li %r14, 255
	cmpldi %cr0, %r17, 0
	beq %cr0, 28f
210:
	rldicl %r14, %r14, 63, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 210b
	b 29f
28:
29:
	ld %r22, 16(%r23)
	subf %r22, %r22, %r28
	ld %r24, 88(%r23)
	ld %r25, 64(%r23)
	addi %r6, %r28, 0
	li %r4, 0
211:
	lbz %r16, 0(%r24)
	li %r0, 0
	subf %r17, %r22, %r4
	rldicl %r17, %r17, 1, 63
	subf %r17, %r17, %r0
	xor %r18, %r4, %r22
	addi %r18, %r18, -1
	rldicl %r18, %r18, 1, 63
	subf %r18, %r18, %r0
	li %r19, 255
	xor %r20, %r19, %r14
	and %r20, %r20, %r18
	xor %r20, %r20, %r19
	or %r20, %r20, %r17
	xor %r20, %r20, %r17
	and %r16, %r16, %r20
	stb %r16, 0(%r25)
	addi %r24, %r24, 1
	addi %r25, %r25, 1
	addi %r4, %r4, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 211b
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	ld %r12, 64(%r23)
	ld %r6, 72(%r23)
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
212:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 212b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
213:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 213b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r23, 256
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
214:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 214b
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
	addi %r8, %r10, 0
	addi %r9, %r10, 0
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
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
215:
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
	bne %cr0, 215b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r23, 256
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
216:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 216b
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	rldicr %r0, %r28, 1, 62
	add %r0, %r0, %r28
	subf %r0, %r0, %r27
	cmpldi %cr0, %r0, 0
	beq %cr0, 217f
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	b 218f
217:
	rldicr %r12, %r28, 1, 62
	add %r12, %r12, %r21
	addi %r6, %r28, 0
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
219:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 219b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
220:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 220b
218:
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
221:
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
	bne %cr0, 221b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r26, %r20, 0
	addi %r10, %r23, 256
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
	li %r3, 0
222:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 222b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r26, %r26, %r19
	xor %r26, %r26, %r19
	cmpldi %cr0, %r26, 0
	beq %cr0, 223f
	ld %r30, 0(%r23)
	ld %r27, 64(%r23)
	ld %r21, 24(%r23)
	li %r3, 1
	rldicl %r9, %r11, 63, 1
	mulld %r9, %r9, %r3
	rldicr %r9, %r9, 3, 60
	add %r8, %r30, %r9
	addi %r8, %r8, 24
	addi %r15, %r8, 0
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
225:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 225b
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
	li %r3, 0
	subf %r12, %r12, %r3
	rldicr %r12, %r12, 32, 31
	rldicl %r12, %r12, 32, 32
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
226:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 226b
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
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	addi %r24, %r21, 0
227:
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
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
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	li %r16, 0
	addi %r19, %r24, -1
	li %r0, 0
	mulld %r18, %r21, %r0
	add %r19, %r19, %r18
	rldicr %r18, %r28, 3, 60
	subf %r18, %r18, %r19
	rldicl %r18, %r18, 1, 63
	cmpldi %cr0, %r18, 0
	beq %cr0, 228f
	rldicl %r18, %r19, 61, 3
	subf %r18, %r18, %r28
	addi %r18, %r18, -1
	add %r17, %r27, %r18
	lbz %r20, 0(%r17)
	li %r0, 7
	and %r18, %r19, %r0
	cmpldi %cr0, %r18, 0
	beq %cr0, 230f
232:
	rldicl %r20, %r20, 63, 1
	addi %r18, %r18, -1
	cmpldi %cr0, %r18, 0
	bne %cr0, 232b
	b 231f
230:
231:
	li %r0, 1
	and %r20, %r20, %r0
	b 229f
228:
	li %r20, 0
229:
	or %r16, %r16, %r20
	addi %r19, %r24, -1
	li %r0, 1
	mulld %r18, %r21, %r0
	add %r19, %r19, %r18
	rldicr %r18, %r28, 3, 60
	subf %r18, %r18, %r19
	rldicl %r18, %r18, 1, 63
	cmpldi %cr0, %r18, 0
	beq %cr0, 233f
	rldicl %r18, %r19, 61, 3
	subf %r18, %r18, %r28
	addi %r18, %r18, -1
	add %r17, %r27, %r18
	lbz %r20, 0(%r17)
	li %r0, 7
	and %r18, %r19, %r0
	cmpldi %cr0, %r18, 0
	beq %cr0, 235f
237:
	rldicl %r20, %r20, 63, 1
	addi %r18, %r18, -1
	cmpldi %cr0, %r18, 0
	bne %cr0, 237b
	b 236f
235:
236:
	li %r0, 1
	and %r20, %r20, %r0
	b 234f
233:
	li %r20, 0
234:
	rldicr %r20, %r20, 1, 62
	or %r16, %r16, %r20
	addi %r19, %r24, -1
	li %r0, 2
	mulld %r18, %r21, %r0
	add %r19, %r19, %r18
	rldicr %r18, %r28, 3, 60
	subf %r18, %r18, %r19
	rldicl %r18, %r18, 1, 63
	cmpldi %cr0, %r18, 0
	beq %cr0, 238f
	rldicl %r18, %r19, 61, 3
	subf %r18, %r18, %r28
	addi %r18, %r18, -1
	add %r17, %r27, %r18
	lbz %r20, 0(%r17)
	li %r0, 7
	and %r18, %r19, %r0
	cmpldi %cr0, %r18, 0
	beq %cr0, 240f
242:
	rldicl %r20, %r20, 63, 1
	addi %r18, %r18, -1
	cmpldi %cr0, %r18, 0
	bne %cr0, 242b
	b 241f
240:
241:
	li %r0, 1
	and %r20, %r20, %r0
	b 239f
238:
	li %r20, 0
239:
	rldicr %r20, %r20, 2, 61
	or %r16, %r16, %r20
	addi %r19, %r24, -1
	li %r0, 3
	mulld %r18, %r21, %r0
	add %r19, %r19, %r18
	rldicr %r18, %r28, 3, 60
	subf %r18, %r18, %r19
	rldicl %r18, %r18, 1, 63
	cmpldi %cr0, %r18, 0
	beq %cr0, 243f
	rldicl %r18, %r19, 61, 3
	subf %r18, %r18, %r28
	addi %r18, %r18, -1
	add %r17, %r27, %r18
	lbz %r20, 0(%r17)
	li %r0, 7
	and %r18, %r19, %r0
	cmpldi %cr0, %r18, 0
	beq %cr0, 245f
247:
	rldicl %r20, %r20, 63, 1
	addi %r18, %r18, -1
	cmpldi %cr0, %r18, 0
	bne %cr0, 247b
	b 246f
245:
246:
	li %r0, 1
	and %r20, %r20, %r0
	b 244f
243:
	li %r20, 0
244:
	rldicr %r20, %r20, 3, 60
	or %r16, %r16, %r20
	addi %r19, %r24, -1
	li %r0, 4
	mulld %r18, %r21, %r0
	add %r19, %r19, %r18
	rldicr %r18, %r28, 3, 60
	subf %r18, %r18, %r19
	rldicl %r18, %r18, 1, 63
	cmpldi %cr0, %r18, 0
	beq %cr0, 248f
	rldicl %r18, %r19, 61, 3
	subf %r18, %r18, %r28
	addi %r18, %r18, -1
	add %r17, %r27, %r18
	lbz %r20, 0(%r17)
	li %r0, 7
	and %r18, %r19, %r0
	cmpldi %cr0, %r18, 0
	beq %cr0, 250f
252:
	rldicl %r20, %r20, 63, 1
	addi %r18, %r18, -1
	cmpldi %cr0, %r18, 0
	bne %cr0, 252b
	b 251f
250:
251:
	li %r0, 1
	and %r20, %r20, %r0
	b 249f
248:
	li %r20, 0
249:
	rldicr %r20, %r20, 4, 59
	or %r16, %r16, %r20
	addi %r26, %r16, 0
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
253:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 253b
	li %r25, 0
254:
	addi %r3, %r25, 2
	rldicl %r9, %r11, 63, 1
	mulld %r9, %r9, %r3
	rldicr %r9, %r9, 3, 60
	add %r8, %r30, %r9
	addi %r8, %r8, 24
	addi %r15, %r8, 0
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
255:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 255b
	xor %r4, %r25, %r26
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r0, 0
	subf %r20, %r4, %r0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
256:
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
	bne %cr0, 256b
	addi %r25, %r25, 1
	addi %r3, %r25, 2
	rldicl %r9, %r11, 63, 1
	mulld %r9, %r9, %r3
	rldicr %r9, %r9, 3, 60
	add %r8, %r30, %r9
	addi %r8, %r8, 24
	addi %r15, %r8, 0
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
257:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 257b
	xor %r4, %r25, %r26
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r0, 0
	subf %r20, %r4, %r0
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
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
258:
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
	bne %cr0, 258b
	addi %r25, %r25, 1
	addi %r3, %r25, -32
	cmpldi %cr0, %r3, 0
	bne %cr0, 254b
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
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
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	addi %r7, %r10, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	addi %r24, %r24, -1
	cmpldi %cr0, %r24, 0
	bne %cr0, 227b
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r6, %r10, 0
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	addi %r31, %r23, 0
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
259:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 259b
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
	addi %r8, %r10, 0
	addi %r9, %r10, 0
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
	add %r10, %r10, %r29
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
	addi %r10, %r23, 256
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
261:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 261b
	li %r26, 0
	addi %r26, %r26, -1
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
	li %r3, 0
262:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 262b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r26, %r26, %r19
	xor %r26, %r26, %r19
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
	li %r3, 0
263:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 263b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r26, %r26, %r19
	xor %r26, %r26, %r19
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
	li %r3, 0
264:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 264b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r26, %r26, %r19
	xor %r26, %r26, %r19
	ld %r27, 80(%r23)
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r28
	addi %r15, %r15, -1
	addi %r16, %r27, 0
	addi %r17, %r28, 0
265:
	lbz %r0, 0(%r15)
	and %r0, %r0, %r26
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 265b
	li %r3, 1
	and %r3, %r3, %r26
	li %r0, 3
	rldicr %r3, %r3, 1, 62
	subf %r3, %r3, %r0
	b 224f
223:
	ld %r27, 80(%r23)
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r28
	addi %r15, %r15, -1
	addi %r16, %r27, 0
	addi %r17, %r28, 0
266:
	lbz %r0, 0(%r15)
	and %r0, %r0, %r26
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 266b
	li %r3, 1
	and %r3, %r3, %r26
	li %r3, 2
224:
	addi %r12, %r3, -1
	li %r0, 0
	subf %r17, %r12, %r0
	or %r17, %r17, %r12
	rldicl %r17, %r17, 1, 63
	addi %r17, %r17, -1
	ld %r25, 64(%r23)
	addi %r6, %r28, 0
267:
	lbz %r16, 0(%r25)
	and %r16, %r16, %r17
	stb %r16, 0(%r25)
	addi %r25, %r25, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 267b
27:
	ld %r14, 112(%r23)
	ld %r15, 120(%r23)
	ld %r16, 128(%r23)
	ld %r17, 136(%r23)
	ld %r18, 144(%r23)
	ld %r19, 152(%r23)
	ld %r20, 160(%r23)
	ld %r21, 168(%r23)
	ld %r22, 176(%r23)
	ld %r24, 184(%r23)
	ld %r25, 192(%r23)
	ld %r26, 200(%r23)
	ld %r27, 208(%r23)
	ld %r28, 216(%r23)
	ld %r29, 224(%r23)
	ld %r30, 232(%r23)
	ld %r31, 240(%r23)
	ld %r23, 248(%r23)
	blr
