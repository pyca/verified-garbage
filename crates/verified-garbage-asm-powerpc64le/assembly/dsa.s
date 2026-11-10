// The functions of `src/dsa.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_derive_key:
	addi %r11, %r10, 0
	std %r14, 104(%r11)
	std %r15, 112(%r11)
	std %r16, 120(%r11)
	std %r17, 128(%r11)
	std %r18, 136(%r11)
	std %r19, 144(%r11)
	std %r20, 152(%r11)
	std %r22, 160(%r11)
	std %r23, 168(%r11)
	std %r24, 176(%r11)
	std %r25, 184(%r11)
	std %r26, 192(%r11)
	std %r27, 200(%r11)
	std %r28, 208(%r11)
	std %r29, 216(%r11)
	std %r30, 224(%r11)
	std %r31, 232(%r11)
	std %r2, 240(%r11)
	std %r21, 248(%r11)
	addi %r21, %r11, 0
	addi %r27, %r5, 0
	addi %r28, %r8, 0
	addi %r26, %r3, 0
	rldicr %r0, %r9, 16, 47
	add %r2, %r7, %r0
	addi %r12, %r27, 0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	addi %r14, %r12, 0
	addi %r17, %r6, 0
	li %r15, 0
	li %r16, 0
20:
	lbz %r0, 0(%r14)
	or %r15, %r15, %r0
	li %r3, 0
	subf %r3, %r15, %r3
	rldicl %r3, %r3, 1, 63
	add %r16, %r16, %r3
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
	cmpldi %cr0, %r16, 0
	beq %cr0, 21f
	add %r14, %r12, %r6
	subf %r14, %r16, %r14
	lbz %r0, 0(%r14)
	rldicl %r0, %r0, 57, 7
	li %r3, 1
	xor %r0, %r0, %r3
	b 22f
21:
	li %r0, 1
22:
	cmpldi %cr0, %r0, 0
	beq %cr0, 23f
	addi %r16, %r26, 0
	rldicr %r17, %r2, 48, 15
	rldicl %r17, %r17, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r0, %r0, %r17
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	li %r0, 0
25:
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 25b
	li %r3, 0
	b 24f
23:
	addi %r24, %r16, 0
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r14, %r12, 0
	addi %r17, %r6, 0
	li %r15, 0
	li %r16, 0
26:
	lbz %r0, 0(%r14)
	or %r15, %r15, %r0
	li %r3, 0
	subf %r3, %r15, %r3
	rldicl %r3, %r3, 1, 63
	add %r16, %r16, %r3
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 26b
	cmpldi %cr0, %r16, 0
	beq %cr0, 27f
	add %r14, %r12, %r6
	subf %r14, %r16, %r14
	lbz %r0, 0(%r14)
	rldicl %r0, %r0, 57, 7
	li %r3, 1
	xor %r0, %r0, %r3
	b 28f
27:
	li %r0, 1
28:
	cmpldi %cr0, %r0, 0
	beq %cr0, 29f
	addi %r16, %r26, 0
	rldicr %r17, %r2, 48, 15
	rldicl %r17, %r17, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r0, %r0, %r17
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	li %r0, 0
211:
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 211b
	li %r3, 0
	b 210f
29:
	addi %r25, %r16, 0
	rldicr %r0, %r16, 32, 31
	add %r2, %r2, %r0
	li %r0, 1
	addi %r3, %r24, -128
	addi %r4, %r25, -20
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 212f
	b 213f
212:
	li %r0, 0
213:
	addi %r3, %r24, -256
	addi %r4, %r25, -20
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 214f
	b 215f
214:
	li %r0, 0
215:
	addi %r3, %r24, -256
	addi %r4, %r25, -28
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 216f
	b 217f
216:
	li %r0, 0
217:
	addi %r3, %r24, -256
	addi %r4, %r25, -32
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 218f
	b 219f
218:
	li %r0, 0
219:
	addi %r3, %r24, -384
	addi %r4, %r25, -32
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 220f
	b 221f
220:
	li %r0, 0
221:
	cmpldi %cr0, %r0, 0
	beq %cr0, 222f
	addi %r16, %r26, 0
	rldicr %r17, %r2, 48, 15
	rldicl %r17, %r17, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r0, %r0, %r17
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	li %r0, 0
224:
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 224b
	li %r3, 0
	b 223f
222:
	addi %r12, %r27, 0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	add %r14, %r12, %r6
	addi %r14, %r14, -1
	lbz %r0, 0(%r14)
	li %r3, 1
	and %r0, %r0, %r3
	xor %r0, %r0, %r3
	cmpldi %cr0, %r0, 0
	beq %cr0, 225f
	addi %r16, %r26, 0
	rldicr %r17, %r2, 48, 15
	rldicl %r17, %r17, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r0, %r0, %r17
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	li %r0, 0
227:
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 227b
	li %r3, 0
	b 226f
225:
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	add %r14, %r12, %r6
	addi %r14, %r14, -1
	lbz %r0, 0(%r14)
	li %r3, 1
	and %r0, %r0, %r3
	xor %r0, %r0, %r3
	cmpldi %cr0, %r0, 0
	beq %cr0, 228f
	addi %r16, %r26, 0
	rldicr %r17, %r2, 48, 15
	rldicl %r17, %r17, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r0, %r0, %r17
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	li %r0, 0
230:
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 230b
	li %r3, 0
	b 229f
228:
	rldicr %r23, %r2, 48, 15
	rldicl %r23, %r23, 16, 48
	li %r11, 28
	mulld %r23, %r23, %r11
	addi %r23, %r23, 704
	add %r23, %r23, %r21
	addi %r31, %r23, 0
	addi %r10, %r23, 256
	li %r11, 8
	li %r29, 48
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
231:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 231b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
232:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 232b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	addi %r30, %r27, 0
	rldicr %r31, %r2, 48, 15
	rldicl %r31, %r31, 16, 48
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
233:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 233b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
234:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
	li %r25, 8
235:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	rldicl %r20, %r24, 1, 63
	rldicr %r24, %r24, 1, 62
236:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 236b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
237:
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
	bne %cr0, 237b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
238:
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
	bne %cr0, 238b
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 235b
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 234b
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
239:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 239b
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
	addi %r14, %r10, 0
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
240:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 240b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r3, %r3, %r0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
	cmpldi %cr0, %r0, 0
	beq %cr0, 241f
	addi %r16, %r26, 0
	rldicr %r17, %r2, 48, 15
	rldicl %r17, %r17, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r0, %r0, %r17
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	li %r0, 0
243:
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 243b
	li %r3, 0
	b 242f
241:
	addi %r23, %r21, 0
	addi %r31, %r21, 0
	addi %r10, %r21, 256
	rldicr %r11, %r2, 48, 15
	rldicl %r11, %r11, 16, 48
	rldicl %r11, %r11, 61, 3
	rldicr %r29, %r11, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r11, 1, 62
	addi %r12, %r27, 0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
244:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 244b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
245:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 245b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	rldicr %r3, %r11, 2, 61
	add %r3, %r10, %r3
	addi %r3, %r3, -8
	ld %r3, 0(%r3)
	cmpldi %cr0, %r3, 0
	beq %cr0, 246f
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
248:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 248b
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	addi %r14, %r14, -8
	li %r0, 1
	std %r0, 0(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r4, %r4, 64
249:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
250:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 250b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
251:
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
	bne %cr0, 251b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
252:
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
	bne %cr0, 252b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 249b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
253:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 253b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
254:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 255f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 257f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 259f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 260f
259:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
260:
	b 258f
257:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
258:
	b 256f
255:
256:
	cmplwi %cr0, %r17, 0
	beq %cr0, 261f
263:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 263b
	b 262f
261:
262:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 254b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
264:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 264b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
265:
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
	bne %cr0, 265b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
266:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 266b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
267:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 268f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 270f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 272f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 273f
272:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
273:
	b 271f
270:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
271:
	b 269f
268:
269:
	cmplwi %cr0, %r17, 0
	beq %cr0, 274f
276:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 276b
	b 275f
274:
275:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 267b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
277:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 277b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
278:
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
	bne %cr0, 278b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
279:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 279b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
280:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 281f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 283f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 285f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 286f
285:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
286:
	b 284f
283:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
284:
	b 282f
281:
282:
	cmplwi %cr0, %r17, 0
	beq %cr0, 287f
289:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 289b
	b 288f
287:
288:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 280b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
290:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 290b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
291:
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
	bne %cr0, 291b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
292:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 292b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
293:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 294f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 296f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 298f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 299f
298:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
299:
	b 297f
296:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
297:
	b 295f
294:
295:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2100f
2102:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 2102b
	b 2101f
2100:
2101:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 293b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2103:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2103b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2104:
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
	bne %cr0, 2104b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
2105:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2105b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
2106:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 2107f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2109f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2111f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 2112f
2111:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
2112:
	b 2110f
2109:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
2110:
	b 2108f
2107:
2108:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2113f
2115:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 2115b
	b 2114f
2113:
2114:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 2106b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2116:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2116b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2117:
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
	bne %cr0, 2117b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
2118:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2118b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
2119:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 2120f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2122f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2124f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 2125f
2124:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
2125:
	b 2123f
2122:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
2123:
	b 2121f
2120:
2121:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2126f
2128:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 2128b
	b 2127f
2126:
2127:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 2119b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2129:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2129b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2130:
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
	bne %cr0, 2130b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2131:
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
	bne %cr0, 2131b
	b 247f
246:
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2132:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2132b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 5, 58
	rldicl %r3, %r11, 63, 1
	add %r4, %r4, %r3
2133:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
2134:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2134b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2135:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2135b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2136:
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
	bne %cr0, 2136b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2133b
	li %r24, 6
2137:
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
2138:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2138b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
2139:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 2140f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2142f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2144f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 2145f
2144:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
2145:
	b 2143f
2142:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
2143:
	b 2141f
2140:
2141:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2146f
2148:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 2148b
	b 2147f
2146:
2147:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 2139b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2149:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2149b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2150:
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
	bne %cr0, 2150b
	addi %r24, %r24, -1
	cmpldi %cr0, %r24, 0
	bne %cr0, 2137b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2151:
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
	bne %cr0, 2151b
247:
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r6
	add %r12, %r12, %r0
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2152:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2152b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2153:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2153b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
	addi %r10, %r31, 256
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2155:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2155b
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2156:
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
	bne %cr0, 2156b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
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
2157:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2157b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
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
2158:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2158b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	addi %r3, %r20, 0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2159f
	b 2160f
2159:
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2161:
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
	bne %cr0, 2161b
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r30, %r12, 0
	addi %r31, %r6, 0
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
2162:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2162b
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2163:
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
	bne %cr0, 2163b
	li %r24, 2
2164:
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
	addi %r19, %r24, 0
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r19, 8
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r5, %r8, 0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2165:
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
	bne %cr0, 2165b
	addi %r24, %r24, 1
	addi %r4, %r24, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2164b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2166:
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
	bne %cr0, 2166b
2167:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2168f
2170:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2170b
	b 2169f
2168:
2169:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2171f
2173:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2173b
	b 2172f
2171:
2172:
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
	rldicr %r24, %r24, 4, 59
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2174f
2176:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2176b
	b 2175f
2174:
2175:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2177f
2179:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2179b
	b 2178f
2177:
2178:
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
	rldicr %r24, %r24, 4, 59
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2167b
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
2180:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2180b
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
2181:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2181b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r3, %r3, %r0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
2160:
	cmpldi %cr0, %r0, 0
	beq %cr0, 2182f
	addi %r16, %r26, 0
	rldicr %r17, %r2, 48, 15
	rldicl %r17, %r17, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r0, %r0, %r17
	add %r17, %r17, %r0
	add %r17, %r17, %r0
	li %r0, 0
2184:
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2184b
	li %r3, 0
	b 2183f
2182:
	addi %r24, %r28, 0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r6
	add %r12, %r12, %r0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2185:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2185b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2186:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2186b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2187:
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
	bne %cr0, 2187b
	addi %r30, %r24, 0
	rldicr %r31, %r2, 32, 31
	rldicl %r31, %r31, 16, 48
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
2188:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2188b
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2189:
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
	bne %cr0, 2189b
	li %r24, 2
2190:
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
	addi %r19, %r24, 0
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r19, 8
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r5, %r8, 0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2191:
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
	bne %cr0, 2191b
	addi %r24, %r24, 1
	addi %r4, %r24, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2190b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2192:
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
	bne %cr0, 2192b
2193:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2194f
2196:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2196b
	b 2195f
2194:
2195:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2197f
2199:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2199b
	b 2198f
2197:
2198:
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
	rldicr %r24, %r24, 4, 59
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2200f
2202:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2202b
	b 2201f
2200:
2201:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2203f
2205:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2205b
	b 2204f
2203:
2204:
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
	rldicr %r24, %r24, 4, 59
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2193b
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
2206:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2206b
	li %r22, 0
	addi %r22, %r22, -1
	li %r20, 0
	addi %r20, %r20, -1
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
2207:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2207b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	and %r22, %r22, %r20
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
2208:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2208b
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
	li %r20, 0
	addi %r20, %r20, -1
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
2209:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2209b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	and %r22, %r22, %r20
	rldicr %r12, %r2, 48, 15
	rldicl %r12, %r12, 16, 48
	li %r0, 28
	mulld %r12, %r12, %r0
	addi %r12, %r12, 704
	add %r12, %r12, %r21
	addi %r12, %r12, 1600
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2210:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2210b
	rldicr %r23, %r2, 48, 15
	rldicl %r23, %r23, 16, 48
	li %r11, 28
	mulld %r23, %r23, %r11
	addi %r23, %r23, 704
	add %r23, %r23, %r21
	addi %r31, %r23, 0
	addi %r10, %r23, 256
	li %r11, 8
	li %r29, 48
	addi %r12, %r28, 0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2211:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2211b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2212:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2212b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2213:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2213b
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2214:
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
	bne %cr0, 2214b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r10, 0
	add %r14, %r14, %r29
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
2215:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2215b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	and %r22, %r22, %r20
	addi %r20, %r22, 0
	addi %r16, %r26, 0
	addi %r14, %r27, 0
	rldicr %r17, %r2, 48, 15
	rldicl %r17, %r17, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r17, %r17, %r17
	add %r17, %r17, %r0
2216:
	lbz %r0, 0(%r14)
	and %r0, %r0, %r20
	stb %r0, 0(%r16)
	addi %r14, %r14, 1
	addi %r16, %r16, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2216b
	rldicr %r12, %r2, 48, 15
	rldicl %r12, %r12, 16, 48
	li %r0, 28
	mulld %r12, %r12, %r0
	addi %r12, %r12, 704
	add %r12, %r12, %r21
	addi %r12, %r12, 1600
	addi %r14, %r12, 0
	rldicr %r17, %r2, 48, 15
	rldicl %r17, %r17, 16, 48
2217:
	lbz %r0, 0(%r14)
	and %r0, %r0, %r20
	stb %r0, 0(%r16)
	addi %r14, %r14, 1
	addi %r16, %r16, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2217b
	addi %r14, %r28, 0
	rldicr %r17, %r2, 32, 31
	rldicl %r17, %r17, 16, 48
2218:
	lbz %r0, 0(%r14)
	and %r0, %r0, %r20
	stb %r0, 0(%r16)
	addi %r14, %r14, 1
	addi %r16, %r16, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2218b
	li %r0, 1
	and %r3, %r20, %r0
2183:
242:
229:
226:
223:
210:
24:
	ld %r14, 104(%r21)
	ld %r15, 112(%r21)
	ld %r16, 120(%r21)
	ld %r17, 128(%r21)
	ld %r18, 136(%r21)
	ld %r19, 144(%r21)
	ld %r20, 152(%r21)
	ld %r22, 160(%r21)
	ld %r23, 168(%r21)
	ld %r24, 176(%r21)
	ld %r25, 184(%r21)
	ld %r26, 192(%r21)
	ld %r27, 200(%r21)
	ld %r28, 208(%r21)
	ld %r29, 216(%r21)
	ld %r30, 224(%r21)
	ld %r31, 232(%r21)
	ld %r2, 240(%r21)
	ld %r21, 248(%r21)
	blr

vg_dsa_sign_random_prevalidated:
	stdu %r1, -304(%r1)
	addi %r12, %r1, 0
	std %r14, 152(%r12)
	std %r15, 160(%r12)
	std %r16, 168(%r12)
	std %r17, 176(%r12)
	std %r18, 184(%r12)
	std %r19, 192(%r12)
	std %r20, 200(%r12)
	std %r21, 208(%r12)
	std %r22, 216(%r12)
	std %r23, 224(%r12)
	std %r24, 232(%r12)
	std %r25, 240(%r12)
	std %r26, 248(%r12)
	std %r27, 256(%r12)
	std %r28, 264(%r12)
	std %r29, 272(%r12)
	std %r30, 280(%r12)
	std %r31, 288(%r12)
	mflr %r0
	std %r0, 296(%r12)
	addi %r18, %r3, 0
	addi %r30, %r5, 0
	addi %r19, %r6, 0
	addi %r20, %r8, 0
	addi %r21, %r9, 0
	addi %r22, %r10, 0
	ld %r23, 408(%r12)
	ld %r24, 416(%r12)
	ld %r3, 400(%r12)
	ld %r4, 424(%r12)
	ld %r5, 432(%r12)
	std %r3, 96(%r12)
	std %r4, 104(%r12)
	std %r5, 112(%r12)
	li %r25, 0
	li %r26, 8
	addi %r12, %r1, 0
	li %r0, 0
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	add %r12, %r19, %r20
	addi %r6, %r21, 0
	addi %r14, %r12, 0
	addi %r17, %r6, 0
	li %r15, 0
	li %r16, 0
20:
	lbz %r0, 0(%r14)
	or %r15, %r15, %r0
	li %r3, 0
	subf %r3, %r15, %r3
	rldicl %r3, %r3, 1, 63
	add %r16, %r16, %r3
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
	addi %r28, %r16, 0
	add %r27, %r12, %r6
	subf %r27, %r16, %r27
	lbz %r3, 0(%r27)
	rldicl %r4, %r3, 63, 1
	or %r29, %r3, %r4
	rldicl %r4, %r29, 62, 2
	or %r29, %r29, %r4
	rldicl %r4, %r29, 60, 4
	or %r29, %r29, %r4
	rldicl %r4, %r16, 63, 1
	rldicl %r5, %r3, 63, 1
	or %r4, %r4, %r5
	li %r5, 0
	subf %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	subf %r5, %r16, %r5
	rldicl %r5, %r5, 1, 63
	and %r0, %r4, %r5
	cmpldi %cr0, %r0, 0
	beq %cr0, 21f
23:
	li %r17, 128
	li %r31, 4
24:
	subf %r3, %r25, %r24
	subf %r4, %r28, %r3
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r3, 1, 63
	li %r5, 1
	xor %r3, %r3, %r5
	and %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 25f
	add %r3, %r23, %r25
	addi %r4, %r1, 120
	add %r4, %r4, %r21
	subf %r4, %r28, %r4
	addi %r5, %r28, 0
	addi %r6, %r29, 0
27:
	lbz %r0, 0(%r3)
	and %r0, %r0, %r6
	stb %r0, 0(%r4)
	li %r6, 255
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 27b
	add %r25, %r25, %r28
	addi %r3, %r1, 120
	add %r3, %r3, %r21
	add %r4, %r27, %r28
	addi %r5, %r28, 0
	li %r6, 0
	li %r7, 0
28:
	addi %r3, %r3, -1
	addi %r4, %r4, -1
	lbz %r0, 0(%r3)
	or %r7, %r7, %r0
	lbz %r8, 0(%r4)
	add %r8, %r8, %r6
	subf %r0, %r8, %r0
	rldicl %r6, %r0, 1, 63
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	li %r0, 0
	subf %r0, %r7, %r0
	rldicl %r0, %r0, 1, 63
	and %r6, %r6, %r0
	cmpldi %cr0, %r6, 0
	bne %cr0, 29f
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	beq %cr0, 211f
	b 212f
211:
	li %r31, 0
212:
	b 210f
29:
	li %r31, 1
210:
	b 26f
25:
	li %r31, 2
26:
	addi %r3, %r31, -4
	cmpldi %cr0, %r3, 0
	beq %cr0, 24b
	addi %r3, %r31, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 213f
	b 214f
213:
	addi %r3, %r18, 0
	add %r4, %r21, %r21
	addi %r5, %r19, 0
	add %r6, %r20, %r20
	add %r6, %r6, %r20
	add %r6, %r6, %r4
	addi %r7, %r20, 0
	addi %r8, %r1, 120
	addi %r9, %r21, 0
	addi %r10, %r22, 0
	bl {vg_dsa_sign_prevalidated}
	cmplwi %cr0, %r3, 0
	beq %cr0, 215f
	li %r31, 1
	b 216f
215:
	addi %r26, %r26, -1
	cmpldi %cr0, %r26, 0
	bne %cr0, 217f
	li %r31, 0
	b 218f
217:
	li %r31, 4
218:
216:
214:
	addi %r3, %r31, -4
	cmpldi %cr0, %r3, 0
	beq %cr0, 23b
	b 22f
21:
	li %r31, 0
22:
	addi %r3, %r31, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 219f
	addi %r16, %r18, 0
	add %r17, %r21, %r21
	li %r0, 0
221:
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 221b
	b 220f
219:
220:
	addi %r12, %r1, 0
	li %r0, 0
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r25, 0(%r30)
	addi %r3, %r31, 0
	addi %r12, %r1, 0
	ld %r0, 296(%r12)
	mtlr %r0
	ld %r14, 152(%r12)
	ld %r15, 160(%r12)
	ld %r16, 168(%r12)
	ld %r17, 176(%r12)
	ld %r18, 184(%r12)
	ld %r19, 192(%r12)
	ld %r20, 200(%r12)
	ld %r21, 208(%r12)
	ld %r22, 216(%r12)
	ld %r23, 224(%r12)
	ld %r24, 232(%r12)
	ld %r25, 240(%r12)
	ld %r26, 248(%r12)
	ld %r27, 256(%r12)
	ld %r28, 264(%r12)
	ld %r29, 272(%r12)
	ld %r30, 280(%r12)
	ld %r31, 288(%r12)
	addi %r1, %r1, 304
	blr

vg_dsa_generate_key:
	stdu %r1, -304(%r1)
	addi %r12, %r1, 0
	std %r14, 152(%r12)
	std %r15, 160(%r12)
	std %r16, 168(%r12)
	std %r17, 176(%r12)
	std %r18, 184(%r12)
	std %r19, 192(%r12)
	std %r20, 200(%r12)
	std %r21, 208(%r12)
	std %r22, 216(%r12)
	std %r23, 224(%r12)
	std %r24, 232(%r12)
	std %r25, 240(%r12)
	std %r26, 248(%r12)
	std %r27, 256(%r12)
	std %r28, 264(%r12)
	std %r29, 272(%r12)
	std %r30, 280(%r12)
	std %r31, 288(%r12)
	mflr %r0
	std %r0, 296(%r12)
	addi %r18, %r3, 0
	addi %r30, %r5, 0
	addi %r19, %r6, 0
	addi %r20, %r8, 0
	addi %r21, %r9, 0
	addi %r23, %r10, 0
	ld %r24, 400(%r12)
	ld %r22, 408(%r12)
	ld %r26, 416(%r12)
	std %r26, 96(%r12)
	li %r25, 0
	addi %r12, %r1, 0
	li %r0, 0
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	addi %r3, %r19, 0
	add %r4, %r20, %r20
	add %r4, %r4, %r21
	addi %r5, %r20, 0
	addi %r6, %r21, 0
	addi %r7, %r22, 0
	addi %r8, %r26, 0
	bl {vg_dsa_check_parameters}
	cmplwi %cr0, %r3, 0
	beq %cr0, 20f
	add %r12, %r19, %r20
	addi %r6, %r21, 0
	addi %r14, %r12, 0
	addi %r17, %r6, 0
	li %r15, 0
	li %r16, 0
22:
	lbz %r0, 0(%r14)
	or %r15, %r15, %r0
	li %r3, 0
	subf %r3, %r15, %r3
	rldicl %r3, %r3, 1, 63
	add %r16, %r16, %r3
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 22b
	addi %r28, %r16, 0
	add %r27, %r12, %r6
	subf %r27, %r16, %r27
	lbz %r3, 0(%r27)
	rldicl %r4, %r3, 63, 1
	or %r29, %r3, %r4
	rldicl %r4, %r29, 62, 2
	or %r29, %r29, %r4
	rldicl %r4, %r29, 60, 4
	or %r29, %r29, %r4
	rldicl %r4, %r16, 63, 1
	rldicl %r5, %r3, 63, 1
	or %r4, %r4, %r5
	li %r5, 0
	subf %r4, %r4, %r5
	rldicl %r4, %r4, 1, 63
	subf %r5, %r16, %r5
	rldicl %r5, %r5, 1, 63
	and %r0, %r4, %r5
	cmpldi %cr0, %r0, 0
	beq %cr0, 23f
	li %r17, 128
	li %r31, 4
25:
	subf %r3, %r25, %r24
	subf %r4, %r28, %r3
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r3, 1, 63
	li %r5, 1
	xor %r3, %r3, %r5
	and %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 26f
	add %r3, %r23, %r25
	addi %r4, %r1, 120
	add %r4, %r4, %r21
	subf %r4, %r28, %r4
	addi %r5, %r28, 0
	addi %r6, %r29, 0
28:
	lbz %r0, 0(%r3)
	and %r0, %r0, %r6
	stb %r0, 0(%r4)
	li %r6, 255
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	add %r25, %r25, %r28
	addi %r3, %r1, 120
	add %r3, %r3, %r21
	add %r4, %r27, %r28
	addi %r5, %r28, 0
	li %r6, 0
	li %r7, 0
29:
	addi %r3, %r3, -1
	addi %r4, %r4, -1
	lbz %r0, 0(%r3)
	or %r7, %r7, %r0
	lbz %r8, 0(%r4)
	add %r8, %r8, %r6
	subf %r0, %r8, %r0
	rldicl %r6, %r0, 1, 63
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 29b
	li %r0, 0
	subf %r0, %r7, %r0
	rldicl %r0, %r0, 1, 63
	and %r6, %r6, %r0
	cmpldi %cr0, %r6, 0
	bne %cr0, 210f
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	beq %cr0, 212f
	b 213f
212:
	li %r31, 0
213:
	b 211f
210:
	li %r31, 1
211:
	b 27f
26:
	li %r31, 2
27:
	addi %r3, %r31, -4
	cmpldi %cr0, %r3, 0
	beq %cr0, 25b
	addi %r3, %r31, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 214f
	b 215f
214:
	addi %r3, %r18, 0
	add %r4, %r20, %r20
	add %r4, %r4, %r20
	add %r4, %r4, %r21
	add %r4, %r4, %r21
	addi %r5, %r19, 0
	add %r6, %r20, %r20
	add %r6, %r6, %r21
	addi %r7, %r20, 0
	addi %r8, %r1, 120
	addi %r9, %r21, 0
	addi %r10, %r22, 0
	bl {vg_dsa_derive_key_checked}
	cmplwi %cr0, %r3, 0
	beq %cr0, 216f
	li %r31, 1
	b 217f
216:
	li %r31, 0
217:
215:
	b 24f
23:
	li %r31, 0
24:
	b 21f
20:
	li %r31, 0
21:
	addi %r3, %r31, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 218f
	addi %r16, %r18, 0
	add %r17, %r20, %r20
	add %r17, %r17, %r20
	add %r17, %r17, %r21
	add %r17, %r17, %r21
	li %r0, 0
220:
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 220b
	b 219f
218:
219:
	addi %r12, %r1, 0
	li %r0, 0
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r25, 0(%r30)
	addi %r3, %r31, 0
	addi %r12, %r1, 0
	ld %r0, 296(%r12)
	mtlr %r0
	ld %r14, 152(%r12)
	ld %r15, 160(%r12)
	ld %r16, 168(%r12)
	ld %r17, 176(%r12)
	ld %r18, 184(%r12)
	ld %r19, 192(%r12)
	ld %r20, 200(%r12)
	ld %r21, 208(%r12)
	ld %r22, 216(%r12)
	ld %r23, 224(%r12)
	ld %r24, 232(%r12)
	ld %r25, 240(%r12)
	ld %r26, 248(%r12)
	ld %r27, 256(%r12)
	ld %r28, 264(%r12)
	ld %r29, 272(%r12)
	ld %r30, 280(%r12)
	ld %r31, 288(%r12)
	addi %r1, %r1, 304
	blr

vg_dsa_validate_public_key:
	addi %r11, %r7, 0
	std %r14, 104(%r11)
	std %r15, 112(%r11)
	std %r16, 120(%r11)
	std %r17, 128(%r11)
	std %r18, 136(%r11)
	std %r19, 144(%r11)
	std %r20, 152(%r11)
	std %r22, 160(%r11)
	std %r23, 168(%r11)
	std %r24, 176(%r11)
	std %r25, 184(%r11)
	std %r26, 192(%r11)
	std %r27, 200(%r11)
	std %r28, 208(%r11)
	std %r29, 216(%r11)
	std %r30, 224(%r11)
	std %r31, 232(%r11)
	std %r2, 240(%r11)
	std %r21, 248(%r11)
	addi %r21, %r11, 0
	addi %r27, %r3, 0
	li %r28, 0
	li %r26, 0
	rldicr %r0, %r6, 16, 47
	add %r2, %r5, %r0
	addi %r12, %r27, 0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	addi %r14, %r12, 0
	addi %r17, %r6, 0
	li %r15, 0
	li %r16, 0
20:
	lbz %r0, 0(%r14)
	or %r15, %r15, %r0
	li %r3, 0
	subf %r3, %r15, %r3
	rldicl %r3, %r3, 1, 63
	add %r16, %r16, %r3
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
	cmpldi %cr0, %r16, 0
	beq %cr0, 21f
	add %r14, %r12, %r6
	subf %r14, %r16, %r14
	lbz %r0, 0(%r14)
	rldicl %r0, %r0, 57, 7
	li %r3, 1
	xor %r0, %r0, %r3
	b 22f
21:
	li %r0, 1
22:
	cmpldi %cr0, %r0, 0
	beq %cr0, 23f
	li %r3, 0
	b 24f
23:
	addi %r24, %r16, 0
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r14, %r12, 0
	addi %r17, %r6, 0
	li %r15, 0
	li %r16, 0
25:
	lbz %r0, 0(%r14)
	or %r15, %r15, %r0
	li %r3, 0
	subf %r3, %r15, %r3
	rldicl %r3, %r3, 1, 63
	add %r16, %r16, %r3
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 25b
	cmpldi %cr0, %r16, 0
	beq %cr0, 26f
	add %r14, %r12, %r6
	subf %r14, %r16, %r14
	lbz %r0, 0(%r14)
	rldicl %r0, %r0, 57, 7
	li %r3, 1
	xor %r0, %r0, %r3
	b 27f
26:
	li %r0, 1
27:
	cmpldi %cr0, %r0, 0
	beq %cr0, 28f
	li %r3, 0
	b 29f
28:
	addi %r25, %r16, 0
	rldicr %r0, %r16, 32, 31
	add %r2, %r2, %r0
	li %r0, 1
	addi %r3, %r24, -128
	addi %r4, %r25, -20
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 210f
	b 211f
210:
	li %r0, 0
211:
	addi %r3, %r24, -256
	addi %r4, %r25, -20
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 212f
	b 213f
212:
	li %r0, 0
213:
	addi %r3, %r24, -256
	addi %r4, %r25, -28
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 214f
	b 215f
214:
	li %r0, 0
215:
	addi %r3, %r24, -256
	addi %r4, %r25, -32
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 216f
	b 217f
216:
	li %r0, 0
217:
	addi %r3, %r24, -384
	addi %r4, %r25, -32
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 218f
	b 219f
218:
	li %r0, 0
219:
	cmpldi %cr0, %r0, 0
	beq %cr0, 220f
	li %r3, 0
	b 221f
220:
	addi %r12, %r27, 0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	add %r14, %r12, %r6
	addi %r14, %r14, -1
	lbz %r0, 0(%r14)
	li %r3, 1
	and %r0, %r0, %r3
	xor %r0, %r0, %r3
	cmpldi %cr0, %r0, 0
	beq %cr0, 222f
	li %r3, 0
	b 223f
222:
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	add %r14, %r12, %r6
	addi %r14, %r14, -1
	lbz %r0, 0(%r14)
	li %r3, 1
	and %r0, %r0, %r3
	xor %r0, %r0, %r3
	cmpldi %cr0, %r0, 0
	beq %cr0, 224f
	li %r3, 0
	b 225f
224:
	rldicr %r23, %r2, 48, 15
	rldicl %r23, %r23, 16, 48
	li %r11, 28
	mulld %r23, %r23, %r11
	addi %r23, %r23, 704
	add %r23, %r23, %r21
	addi %r31, %r23, 0
	addi %r10, %r23, 256
	li %r11, 8
	li %r29, 48
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
226:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 226b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
227:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 227b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	addi %r30, %r27, 0
	rldicr %r31, %r2, 48, 15
	rldicl %r31, %r31, 16, 48
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
228:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 228b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
229:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
	li %r25, 8
230:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	rldicl %r20, %r24, 1, 63
	rldicr %r24, %r24, 1, 62
231:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 231b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
232:
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
	bne %cr0, 232b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
233:
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
	bne %cr0, 233b
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 230b
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
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
234:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 234b
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
	addi %r14, %r10, 0
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
235:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 235b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r3, %r3, %r0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
	cmpldi %cr0, %r0, 0
	beq %cr0, 236f
	li %r3, 0
	b 237f
236:
	addi %r23, %r21, 0
	addi %r31, %r21, 0
	addi %r10, %r21, 256
	rldicr %r11, %r2, 48, 15
	rldicl %r11, %r11, 16, 48
	rldicl %r11, %r11, 61, 3
	rldicr %r29, %r11, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r11, 1, 62
	addi %r12, %r27, 0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
238:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 238b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
239:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 239b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	rldicr %r3, %r11, 2, 61
	add %r3, %r10, %r3
	addi %r3, %r3, -8
	ld %r3, 0(%r3)
	cmpldi %cr0, %r3, 0
	beq %cr0, 240f
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
242:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 242b
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	addi %r14, %r14, -8
	li %r0, 1
	std %r0, 0(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r4, %r4, 64
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
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
247:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 247b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
248:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 249f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 251f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 253f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 254f
253:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
254:
	b 252f
251:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
252:
	b 250f
249:
250:
	cmplwi %cr0, %r17, 0
	beq %cr0, 255f
257:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 257b
	b 256f
255:
256:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 248b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
258:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 258b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
259:
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
	bne %cr0, 259b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
260:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 260b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
261:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 262f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 264f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 266f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 267f
266:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
267:
	b 265f
264:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
265:
	b 263f
262:
263:
	cmplwi %cr0, %r17, 0
	beq %cr0, 268f
270:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 270b
	b 269f
268:
269:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 261b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
271:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 271b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
272:
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
	bne %cr0, 272b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
273:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 273b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
274:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 275f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 277f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 279f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 280f
279:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
280:
	b 278f
277:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
278:
	b 276f
275:
276:
	cmplwi %cr0, %r17, 0
	beq %cr0, 281f
283:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 283b
	b 282f
281:
282:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 274b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
284:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 284b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
285:
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
	bne %cr0, 285b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
286:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 286b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
287:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 288f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 290f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 292f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 293f
292:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
293:
	b 291f
290:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
291:
	b 289f
288:
289:
	cmplwi %cr0, %r17, 0
	beq %cr0, 294f
296:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 296b
	b 295f
294:
295:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 287b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
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
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
299:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 299b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
2100:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 2101f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2103f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2105f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 2106f
2105:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
2106:
	b 2104f
2103:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
2104:
	b 2102f
2101:
2102:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2107f
2109:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 2109b
	b 2108f
2107:
2108:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 2100b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2110:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2110b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2111:
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
	bne %cr0, 2111b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
2112:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2112b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
2113:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 2114f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2116f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2118f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 2119f
2118:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
2119:
	b 2117f
2116:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
2117:
	b 2115f
2114:
2115:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2120f
2122:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 2122b
	b 2121f
2120:
2121:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 2113b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2123:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2123b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2124:
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
	bne %cr0, 2124b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2125:
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
	bne %cr0, 2125b
	b 241f
240:
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2126:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2126b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 5, 58
	rldicl %r3, %r11, 63, 1
	add %r4, %r4, %r3
2127:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
2128:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2128b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2129:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2129b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2130:
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
	bne %cr0, 2130b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2127b
	li %r24, 6
2131:
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
2132:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2132b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
2133:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 2134f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2136f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2138f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 2139f
2138:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
2139:
	b 2137f
2136:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
2137:
	b 2135f
2134:
2135:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2140f
2142:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 2142b
	b 2141f
2140:
2141:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 2133b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2143:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2143b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2144:
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
	bne %cr0, 2144b
	addi %r24, %r24, -1
	cmpldi %cr0, %r24, 0
	bne %cr0, 2131b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2145:
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
	bne %cr0, 2145b
241:
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r6
	add %r12, %r12, %r0
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2146:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2146b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2147:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2147b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2148:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2148b
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
	addi %r10, %r31, 256
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2149:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2149b
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2150:
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
	bne %cr0, 2150b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
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
2151:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2151b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
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
2152:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2152b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	addi %r3, %r20, 0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2153f
	b 2154f
2153:
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2155:
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
	bne %cr0, 2155b
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r30, %r12, 0
	addi %r31, %r6, 0
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
2156:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2156b
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2157:
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
	bne %cr0, 2157b
	li %r24, 2
2158:
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
	addi %r19, %r24, 0
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r19, 8
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r5, %r8, 0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2159:
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
	bne %cr0, 2159b
	addi %r24, %r24, 1
	addi %r4, %r24, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2158b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2160:
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
	bne %cr0, 2160b
2161:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2162f
2164:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2164b
	b 2163f
2162:
2163:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2165f
2167:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2167b
	b 2166f
2165:
2166:
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
	rldicr %r24, %r24, 4, 59
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2168f
2170:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2170b
	b 2169f
2168:
2169:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2171f
2173:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2173b
	b 2172f
2171:
2172:
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
	rldicr %r24, %r24, 4, 59
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2161b
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
2174:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2174b
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
2175:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2175b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r3, %r3, %r0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
2154:
	cmpldi %cr0, %r0, 0
	beq %cr0, 2176f
	li %r3, 0
	b 2177f
2176:
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r6
	add %r12, %r12, %r0
	add %r12, %r12, %r6
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2178:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2178b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2179:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2179b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2180:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2180b
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
	addi %r10, %r31, 256
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2181:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2181b
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2182:
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
	bne %cr0, 2182b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
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
2183:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2183b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
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
2184:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2184b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	addi %r3, %r20, 0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2185f
	b 2186f
2185:
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2187:
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
	bne %cr0, 2187b
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r30, %r12, 0
	addi %r31, %r6, 0
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
2188:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2188b
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2189:
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
	bne %cr0, 2189b
	li %r24, 2
2190:
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
	addi %r19, %r24, 0
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r19, 8
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r5, %r8, 0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2191:
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
	bne %cr0, 2191b
	addi %r24, %r24, 1
	addi %r4, %r24, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2190b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2192:
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
	bne %cr0, 2192b
2193:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2194f
2196:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2196b
	b 2195f
2194:
2195:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2197f
2199:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2199b
	b 2198f
2197:
2198:
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
	rldicr %r24, %r24, 4, 59
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2200f
2202:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2202b
	b 2201f
2200:
2201:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2203f
2205:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2205b
	b 2204f
2203:
2204:
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
	rldicr %r24, %r24, 4, 59
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2193b
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
2206:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2206b
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
2207:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2207b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r3, %r3, %r0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
2186:
	cmpldi %cr0, %r0, 0
	beq %cr0, 2208f
	li %r3, 0
	b 2209f
2208:
	li %r3, 1
2209:
2177:
237:
225:
223:
221:
29:
24:
	ld %r14, 104(%r21)
	ld %r15, 112(%r21)
	ld %r16, 120(%r21)
	ld %r17, 128(%r21)
	ld %r18, 136(%r21)
	ld %r19, 144(%r21)
	ld %r20, 152(%r21)
	ld %r22, 160(%r21)
	ld %r23, 168(%r21)
	ld %r24, 176(%r21)
	ld %r25, 184(%r21)
	ld %r26, 192(%r21)
	ld %r27, 200(%r21)
	ld %r28, 208(%r21)
	ld %r29, 216(%r21)
	ld %r30, 224(%r21)
	ld %r31, 232(%r21)
	ld %r2, 240(%r21)
	ld %r21, 248(%r21)
	blr

vg_dsa_validate_private_key:
	addi %r11, %r7, 0
	std %r14, 104(%r11)
	std %r15, 112(%r11)
	std %r16, 120(%r11)
	std %r17, 128(%r11)
	std %r18, 136(%r11)
	std %r19, 144(%r11)
	std %r20, 152(%r11)
	std %r22, 160(%r11)
	std %r23, 168(%r11)
	std %r24, 176(%r11)
	std %r25, 184(%r11)
	std %r26, 192(%r11)
	std %r27, 200(%r11)
	std %r28, 208(%r11)
	std %r29, 216(%r11)
	std %r30, 224(%r11)
	std %r31, 232(%r11)
	std %r2, 240(%r11)
	std %r21, 248(%r11)
	addi %r21, %r11, 0
	addi %r27, %r3, 0
	li %r28, 0
	li %r26, 0
	rldicr %r0, %r6, 16, 47
	add %r2, %r5, %r0
	addi %r12, %r27, 0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	addi %r14, %r12, 0
	addi %r17, %r6, 0
	li %r15, 0
	li %r16, 0
20:
	lbz %r0, 0(%r14)
	or %r15, %r15, %r0
	li %r3, 0
	subf %r3, %r15, %r3
	rldicl %r3, %r3, 1, 63
	add %r16, %r16, %r3
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
	cmpldi %cr0, %r16, 0
	beq %cr0, 21f
	add %r14, %r12, %r6
	subf %r14, %r16, %r14
	lbz %r0, 0(%r14)
	rldicl %r0, %r0, 57, 7
	li %r3, 1
	xor %r0, %r0, %r3
	b 22f
21:
	li %r0, 1
22:
	cmpldi %cr0, %r0, 0
	beq %cr0, 23f
	li %r3, 0
	b 24f
23:
	addi %r24, %r16, 0
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r14, %r12, 0
	addi %r17, %r6, 0
	li %r15, 0
	li %r16, 0
25:
	lbz %r0, 0(%r14)
	or %r15, %r15, %r0
	li %r3, 0
	subf %r3, %r15, %r3
	rldicl %r3, %r3, 1, 63
	add %r16, %r16, %r3
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 25b
	cmpldi %cr0, %r16, 0
	beq %cr0, 26f
	add %r14, %r12, %r6
	subf %r14, %r16, %r14
	lbz %r0, 0(%r14)
	rldicl %r0, %r0, 57, 7
	li %r3, 1
	xor %r0, %r0, %r3
	b 27f
26:
	li %r0, 1
27:
	cmpldi %cr0, %r0, 0
	beq %cr0, 28f
	li %r3, 0
	b 29f
28:
	addi %r25, %r16, 0
	rldicr %r0, %r16, 32, 31
	add %r2, %r2, %r0
	li %r0, 1
	addi %r3, %r24, -128
	addi %r4, %r25, -20
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 210f
	b 211f
210:
	li %r0, 0
211:
	addi %r3, %r24, -256
	addi %r4, %r25, -20
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 212f
	b 213f
212:
	li %r0, 0
213:
	addi %r3, %r24, -256
	addi %r4, %r25, -28
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 214f
	b 215f
214:
	li %r0, 0
215:
	addi %r3, %r24, -256
	addi %r4, %r25, -32
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 216f
	b 217f
216:
	li %r0, 0
217:
	addi %r3, %r24, -384
	addi %r4, %r25, -32
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 218f
	b 219f
218:
	li %r0, 0
219:
	cmpldi %cr0, %r0, 0
	beq %cr0, 220f
	li %r3, 0
	b 221f
220:
	addi %r12, %r27, 0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	add %r14, %r12, %r6
	addi %r14, %r14, -1
	lbz %r0, 0(%r14)
	li %r3, 1
	and %r0, %r0, %r3
	xor %r0, %r0, %r3
	cmpldi %cr0, %r0, 0
	beq %cr0, 222f
	li %r3, 0
	b 223f
222:
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	add %r14, %r12, %r6
	addi %r14, %r14, -1
	lbz %r0, 0(%r14)
	li %r3, 1
	and %r0, %r0, %r3
	xor %r0, %r0, %r3
	cmpldi %cr0, %r0, 0
	beq %cr0, 224f
	li %r3, 0
	b 225f
224:
	rldicr %r23, %r2, 48, 15
	rldicl %r23, %r23, 16, 48
	li %r11, 28
	mulld %r23, %r23, %r11
	addi %r23, %r23, 704
	add %r23, %r23, %r21
	addi %r31, %r23, 0
	addi %r10, %r23, 256
	li %r11, 8
	li %r29, 48
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
226:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 226b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
227:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 227b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	addi %r30, %r27, 0
	rldicr %r31, %r2, 48, 15
	rldicl %r31, %r31, 16, 48
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
228:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 228b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
229:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
	li %r25, 8
230:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	rldicl %r20, %r24, 1, 63
	rldicr %r24, %r24, 1, 62
231:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 231b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
232:
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
	bne %cr0, 232b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
233:
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
	bne %cr0, 233b
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 230b
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 229b
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
234:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 234b
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
	addi %r14, %r10, 0
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
235:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 235b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r3, %r3, %r0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
	cmpldi %cr0, %r0, 0
	beq %cr0, 236f
	li %r3, 0
	b 237f
236:
	addi %r23, %r21, 0
	addi %r31, %r21, 0
	addi %r10, %r21, 256
	rldicr %r11, %r2, 48, 15
	rldicl %r11, %r11, 16, 48
	rldicl %r11, %r11, 61, 3
	rldicr %r29, %r11, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r11, 1, 62
	addi %r12, %r27, 0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
238:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 238b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
239:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 239b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	rldicr %r3, %r11, 2, 61
	add %r3, %r10, %r3
	addi %r3, %r3, -8
	ld %r3, 0(%r3)
	cmpldi %cr0, %r3, 0
	beq %cr0, 240f
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
242:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 242b
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	addi %r14, %r14, -8
	li %r0, 1
	std %r0, 0(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r4, %r4, 64
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
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
247:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 247b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
248:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 249f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 251f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 253f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 254f
253:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
254:
	b 252f
251:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
252:
	b 250f
249:
250:
	cmplwi %cr0, %r17, 0
	beq %cr0, 255f
257:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 257b
	b 256f
255:
256:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 248b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
258:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 258b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
259:
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
	bne %cr0, 259b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
260:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 260b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
261:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 262f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 264f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 266f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 267f
266:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
267:
	b 265f
264:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
265:
	b 263f
262:
263:
	cmplwi %cr0, %r17, 0
	beq %cr0, 268f
270:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 270b
	b 269f
268:
269:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 261b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
271:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 271b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
272:
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
	bne %cr0, 272b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
273:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 273b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
274:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 275f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 277f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 279f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 280f
279:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
280:
	b 278f
277:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
278:
	b 276f
275:
276:
	cmplwi %cr0, %r17, 0
	beq %cr0, 281f
283:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 283b
	b 282f
281:
282:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 274b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
284:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 284b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
285:
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
	bne %cr0, 285b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
286:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 286b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
287:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 288f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 290f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 292f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 293f
292:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
293:
	b 291f
290:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
291:
	b 289f
288:
289:
	cmplwi %cr0, %r17, 0
	beq %cr0, 294f
296:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 296b
	b 295f
294:
295:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 287b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
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
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
299:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 299b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
2100:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 2101f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2103f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2105f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 2106f
2105:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
2106:
	b 2104f
2103:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
2104:
	b 2102f
2101:
2102:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2107f
2109:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 2109b
	b 2108f
2107:
2108:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 2100b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2110:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2110b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2111:
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
	bne %cr0, 2111b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
2112:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2112b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
2113:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 2114f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2116f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2118f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 2119f
2118:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
2119:
	b 2117f
2116:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
2117:
	b 2115f
2114:
2115:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2120f
2122:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 2122b
	b 2121f
2120:
2121:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 2113b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2123:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2123b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2124:
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
	bne %cr0, 2124b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2125:
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
	bne %cr0, 2125b
	b 241f
240:
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2126:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2126b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 5, 58
	rldicl %r3, %r11, 63, 1
	add %r4, %r4, %r3
2127:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
2128:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2128b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2129:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2129b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2130:
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
	bne %cr0, 2130b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2127b
	li %r24, 6
2131:
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
2132:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2132b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
2133:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 2134f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2136f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2138f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 2139f
2138:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
2139:
	b 2137f
2136:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
2137:
	b 2135f
2134:
2135:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2140f
2142:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 2142b
	b 2141f
2140:
2141:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 2133b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2143:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2143b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2144:
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
	bne %cr0, 2144b
	addi %r24, %r24, -1
	cmpldi %cr0, %r24, 0
	bne %cr0, 2131b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2145:
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
	bne %cr0, 2145b
241:
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r6
	add %r12, %r12, %r0
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2146:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2146b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2147:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2147b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2148:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2148b
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
	addi %r10, %r31, 256
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2149:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2149b
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2150:
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
	bne %cr0, 2150b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
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
2151:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2151b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
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
2152:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2152b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	addi %r3, %r20, 0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2153f
	b 2154f
2153:
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2155:
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
	bne %cr0, 2155b
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r30, %r12, 0
	addi %r31, %r6, 0
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
2156:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2156b
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2157:
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
	bne %cr0, 2157b
	li %r24, 2
2158:
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
	addi %r19, %r24, 0
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r19, 8
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r5, %r8, 0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2159:
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
	bne %cr0, 2159b
	addi %r24, %r24, 1
	addi %r4, %r24, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2158b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2160:
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
	bne %cr0, 2160b
2161:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2162f
2164:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2164b
	b 2163f
2162:
2163:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2165f
2167:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2167b
	b 2166f
2165:
2166:
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
	rldicr %r24, %r24, 4, 59
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2168f
2170:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2170b
	b 2169f
2168:
2169:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2171f
2173:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2173b
	b 2172f
2171:
2172:
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
	rldicr %r24, %r24, 4, 59
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2161b
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
2174:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2174b
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
2175:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2175b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r3, %r3, %r0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
2154:
	cmpldi %cr0, %r0, 0
	beq %cr0, 2176f
	li %r3, 0
	b 2177f
2176:
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r6
	add %r12, %r12, %r0
	add %r12, %r12, %r6
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2178:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2178b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2179:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2179b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2180:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2180b
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
	addi %r10, %r31, 256
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2181:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2181b
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2182:
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
	bne %cr0, 2182b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
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
2183:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2183b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
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
2184:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2184b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	addi %r3, %r20, 0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2185f
	b 2186f
2185:
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2187:
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
	bne %cr0, 2187b
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r30, %r12, 0
	addi %r31, %r6, 0
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
2188:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2188b
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2189:
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
	bne %cr0, 2189b
	li %r24, 2
2190:
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
	addi %r19, %r24, 0
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r19, 8
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r5, %r8, 0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2191:
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
	bne %cr0, 2191b
	addi %r24, %r24, 1
	addi %r4, %r24, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2190b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2192:
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
	bne %cr0, 2192b
2193:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2194f
2196:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2196b
	b 2195f
2194:
2195:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2197f
2199:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2199b
	b 2198f
2197:
2198:
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
	rldicr %r24, %r24, 4, 59
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2200f
2202:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2202b
	b 2201f
2200:
2201:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2203f
2205:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2205b
	b 2204f
2203:
2204:
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
	rldicr %r24, %r24, 4, 59
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2193b
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
2206:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2206b
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
2207:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2207b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r3, %r3, %r0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
2186:
	cmpldi %cr0, %r0, 0
	beq %cr0, 2208f
	li %r3, 0
	b 2209f
2208:
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r6
	add %r12, %r12, %r0
	add %r12, %r12, %r6
	add %r12, %r12, %r6
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r24, %r12, 0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r6
	add %r12, %r12, %r0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2210:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2210b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2211:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2211b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2212:
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
	bne %cr0, 2212b
	addi %r30, %r24, 0
	rldicr %r31, %r2, 32, 31
	rldicl %r31, %r31, 16, 48
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
2213:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2213b
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2214:
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
	bne %cr0, 2214b
	li %r24, 2
2215:
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
	addi %r19, %r24, 0
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r19, 8
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r5, %r8, 0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2216:
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
	bne %cr0, 2216b
	addi %r24, %r24, 1
	addi %r4, %r24, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2215b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2217:
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
	bne %cr0, 2217b
2218:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2219f
2221:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2221b
	b 2220f
2219:
2220:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2222f
2224:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2224b
	b 2223f
2222:
2223:
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
	rldicr %r24, %r24, 4, 59
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
	rldicl %r18, %r24, 4, 60
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2225f
2227:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2227b
	b 2226f
2225:
2226:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2228f
2230:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2230b
	b 2229f
2228:
2229:
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
	rldicr %r24, %r24, 4, 59
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2218b
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
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r6
	add %r12, %r12, %r0
	add %r12, %r12, %r6
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2231:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2231b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2232:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2232b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2233:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2233b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r3, %r3, %r0
	std %r3, 0(%r21)
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r6
	add %r12, %r12, %r0
	add %r12, %r12, %r6
	add %r12, %r12, %r6
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	ld %r22, 0(%r21)
	addi %r28, %r12, 0
	rldicr %r23, %r2, 48, 15
	rldicl %r23, %r23, 16, 48
	li %r11, 28
	mulld %r23, %r23, %r11
	addi %r23, %r23, 704
	add %r23, %r23, %r21
	addi %r31, %r23, 0
	addi %r10, %r23, 256
	li %r11, 8
	li %r29, 48
	addi %r12, %r28, 0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2234:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2234b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2235:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2235b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2236:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2236b
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2237:
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
	bne %cr0, 2237b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r10, 0
	add %r14, %r14, %r29
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
2238:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2238b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	and %r22, %r22, %r20
	addi %r20, %r22, 0
	li %r0, 1
	and %r3, %r20, %r0
2209:
2177:
237:
225:
223:
221:
29:
24:
	ld %r14, 104(%r21)
	ld %r15, 112(%r21)
	ld %r16, 120(%r21)
	ld %r17, 128(%r21)
	ld %r18, 136(%r21)
	ld %r19, 144(%r21)
	ld %r20, 152(%r21)
	ld %r22, 160(%r21)
	ld %r23, 168(%r21)
	ld %r24, 176(%r21)
	ld %r25, 184(%r21)
	ld %r26, 192(%r21)
	ld %r27, 200(%r21)
	ld %r28, 208(%r21)
	ld %r29, 216(%r21)
	ld %r30, 224(%r21)
	ld %r31, 232(%r21)
	ld %r2, 240(%r21)
	ld %r21, 248(%r21)
	blr

vg_dsa_verify_prevalidated:
	addi %r11, %r1, 96
	ld %r11, 0(%r11)
	std %r14, 104(%r11)
	std %r15, 112(%r11)
	std %r16, 120(%r11)
	std %r17, 128(%r11)
	std %r18, 136(%r11)
	std %r19, 144(%r11)
	std %r20, 152(%r11)
	std %r22, 160(%r11)
	std %r23, 168(%r11)
	std %r24, 176(%r11)
	std %r25, 184(%r11)
	std %r26, 192(%r11)
	std %r27, 200(%r11)
	std %r28, 208(%r11)
	std %r29, 216(%r11)
	std %r30, 224(%r11)
	std %r31, 232(%r11)
	std %r2, 240(%r11)
	std %r21, 248(%r11)
	addi %r21, %r11, 0
	addi %r27, %r3, 0
	addi %r28, %r7, 0
	addi %r26, %r9, 0
	rldicl %r4, %r10, 58, 6
	li %r0, 0
	subf %r4, %r4, %r0
	rldicl %r4, %r4, 1, 63
	subf %r4, %r4, %r0
	li %r0, 64
	xor %r0, %r10, %r0
	and %r0, %r0, %r4
	xor %r4, %r10, %r0
	rldicr %r4, %r4, 48, 15
	rldicr %r0, %r6, 16, 47
	add %r2, %r5, %r0
	add %r2, %r2, %r4
	addi %r12, %r27, 0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	addi %r14, %r12, 0
	addi %r17, %r6, 0
	li %r15, 0
	li %r16, 0
20:
	lbz %r0, 0(%r14)
	or %r15, %r15, %r0
	li %r3, 0
	subf %r3, %r15, %r3
	rldicl %r3, %r3, 1, 63
	add %r16, %r16, %r3
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
	cmpldi %cr0, %r16, 0
	beq %cr0, 21f
	add %r14, %r12, %r6
	subf %r14, %r16, %r14
	lbz %r0, 0(%r14)
	rldicl %r0, %r0, 57, 7
	li %r3, 1
	xor %r0, %r0, %r3
	b 22f
21:
	li %r0, 1
22:
	cmpldi %cr0, %r0, 0
	beq %cr0, 23f
	li %r3, 0
	b 24f
23:
	addi %r24, %r16, 0
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r14, %r12, 0
	addi %r17, %r6, 0
	li %r15, 0
	li %r16, 0
25:
	lbz %r0, 0(%r14)
	or %r15, %r15, %r0
	li %r3, 0
	subf %r3, %r15, %r3
	rldicl %r3, %r3, 1, 63
	add %r16, %r16, %r3
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 25b
	cmpldi %cr0, %r16, 0
	beq %cr0, 26f
	add %r14, %r12, %r6
	subf %r14, %r16, %r14
	lbz %r0, 0(%r14)
	rldicl %r0, %r0, 57, 7
	li %r3, 1
	xor %r0, %r0, %r3
	b 27f
26:
	li %r0, 1
27:
	cmpldi %cr0, %r0, 0
	beq %cr0, 28f
	li %r3, 0
	b 29f
28:
	addi %r25, %r16, 0
	rldicr %r0, %r16, 32, 31
	add %r2, %r2, %r0
	li %r0, 1
	addi %r3, %r24, -128
	addi %r4, %r25, -20
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 210f
	b 211f
210:
	li %r0, 0
211:
	addi %r3, %r24, -256
	addi %r4, %r25, -20
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 212f
	b 213f
212:
	li %r0, 0
213:
	addi %r3, %r24, -256
	addi %r4, %r25, -28
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 214f
	b 215f
214:
	li %r0, 0
215:
	addi %r3, %r24, -256
	addi %r4, %r25, -32
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 216f
	b 217f
216:
	li %r0, 0
217:
	addi %r3, %r24, -384
	addi %r4, %r25, -32
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	beq %cr0, 218f
	b 219f
218:
	li %r0, 0
219:
	cmpldi %cr0, %r0, 0
	beq %cr0, 220f
	li %r3, 0
	b 221f
220:
	rldicr %r23, %r2, 48, 15
	rldicl %r23, %r23, 16, 48
	li %r11, 28
	mulld %r23, %r23, %r11
	addi %r23, %r23, 704
	add %r23, %r23, %r21
	addi %r31, %r23, 0
	addi %r10, %r23, 256
	li %r11, 8
	li %r29, 48
	rldicr %r0, %r2, 48, 15
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
222:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 222b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
223:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 223b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	addi %r23, %r21, 0
	addi %r31, %r21, 0
	addi %r10, %r21, 256
	rldicr %r11, %r2, 48, 15
	rldicl %r11, %r11, 16, 48
	rldicl %r11, %r11, 61, 3
	rldicr %r29, %r11, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r11, 1, 62
	addi %r12, %r27, 0
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
224:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 224b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
225:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 225b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	rldicr %r3, %r11, 2, 61
	add %r3, %r10, %r3
	addi %r3, %r3, -8
	ld %r3, 0(%r3)
	cmpldi %cr0, %r3, 0
	beq %cr0, 226f
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
228:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 228b
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	addi %r14, %r14, -8
	li %r0, 1
	std %r0, 0(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r4, %r4, 64
229:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
230:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 230b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
231:
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
	bne %cr0, 231b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
232:
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
	bne %cr0, 232b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 229b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
233:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 233b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
234:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 235f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 237f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 239f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 240f
239:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
240:
	b 238f
237:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
238:
	b 236f
235:
236:
	cmplwi %cr0, %r17, 0
	beq %cr0, 241f
243:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 243b
	b 242f
241:
242:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 234b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
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
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
246:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 246b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
247:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 248f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 250f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 252f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 253f
252:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
253:
	b 251f
250:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
251:
	b 249f
248:
249:
	cmplwi %cr0, %r17, 0
	beq %cr0, 254f
256:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 256b
	b 255f
254:
255:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 247b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
257:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 257b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
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
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
259:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 259b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
260:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 261f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 263f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 265f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 266f
265:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
266:
	b 264f
263:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
264:
	b 262f
261:
262:
	cmplwi %cr0, %r17, 0
	beq %cr0, 267f
269:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 269b
	b 268f
267:
268:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 260b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
270:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 270b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
271:
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
	bne %cr0, 271b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
272:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 272b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
273:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 274f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 276f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 278f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 279f
278:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
279:
	b 277f
276:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
277:
	b 275f
274:
275:
	cmplwi %cr0, %r17, 0
	beq %cr0, 280f
282:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 282b
	b 281f
280:
281:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 273b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
283:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 283b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
284:
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
	bne %cr0, 284b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
285:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 285b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
286:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 287f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 289f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 291f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 292f
291:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
292:
	b 290f
289:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
290:
	b 288f
287:
288:
	cmplwi %cr0, %r17, 0
	beq %cr0, 293f
295:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 295b
	b 294f
293:
294:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 286b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
296:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 296b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
297:
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
	bne %cr0, 297b
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
298:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 298b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
299:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 2100f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2102f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2104f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 2105f
2104:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
2105:
	b 2103f
2102:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
2103:
	b 2101f
2100:
2101:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2106f
2108:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 2108b
	b 2107f
2106:
2107:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 299b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
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
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2111:
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
	bne %cr0, 2111b
	b 227f
226:
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2112:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2112b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 5, 58
	rldicl %r3, %r11, 63, 1
	add %r4, %r4, %r3
2113:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
2114:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2114b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2115:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2115b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2116:
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
	bne %cr0, 2116b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2113b
	li %r24, 6
2117:
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
2118:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2118b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
2119:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 2120f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2122f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2124f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 2125f
2124:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
2125:
	b 2123f
2122:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
2123:
	b 2121f
2120:
2121:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2126f
2128:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 2128b
	b 2127f
2126:
2127:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 2119b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2129:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2129b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2130:
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
	bne %cr0, 2130b
	addi %r24, %r24, -1
	cmpldi %cr0, %r24, 0
	bne %cr0, 2117b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2131:
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
	bne %cr0, 2131b
227:
	rldicr %r23, %r2, 48, 15
	rldicl %r23, %r23, 16, 48
	li %r11, 28
	mulld %r23, %r23, %r11
	addi %r23, %r23, 704
	add %r23, %r23, %r21
	addi %r31, %r23, 0
	addi %r10, %r23, 256
	li %r11, 8
	li %r29, 48
	addi %r12, %r28, 0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2132:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2132b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2133:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2133b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	addi %r12, %r28, 0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	add %r12, %r12, %r6
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2134:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2134b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2135:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2135b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2136:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2136b
	li %r22, 0
	addi %r22, %r22, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2137:
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
	bne %cr0, 2137b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r10, 0
	add %r14, %r14, %r29
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
2138:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2138b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	and %r22, %r22, %r20
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2139:
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
	bne %cr0, 2139b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
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
2140:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2140b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	and %r22, %r22, %r20
	std %r22, 0(%r21)
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
2141:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2141b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 5, 58
	rldicl %r3, %r11, 63, 1
	add %r4, %r4, %r3
2142:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
2143:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2143b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2144:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2144b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2145:
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
	bne %cr0, 2145b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2142b
	li %r24, 6
2146:
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r6, %r10, 0
	add %r6, %r6, %r3
	addi %r7, %r10, 0
	add %r7, %r7, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
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
2147:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2147b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
2148:
	subf %r9, %r10, %r16
	addi %r16, %r10, 0
	subf %r15, %r9, %r15
	add %r3, %r9, %r9
	add %r3, %r3, %r10
	addi %r14, %r3, 32
	add %r4, %r3, %r9
	ld %r19, 40(%r4)
	rldicl %r7, %r9, 61, 3
	addi %r7, %r7, -1
	rldicl %r8, %r7, 62, 2
	add %r17, %r17, %r8
	rldicr %r9, %r7, 62, 1
	rldicl %r9, %r9, 2, 62
	ld %r18, 0(%r6)
	addi %r6, %r6, 8
	ld %r3, 0(%r14)
	ld %r0, 0(%r15)
	mulhdu %r20, %r18, %r0
	mulld %r0, %r18, %r0
	addc %r3, %r3, %r0
	subfe %r12, %r12, %r12
	mulld %r19, %r19, %r3
	ld %r0, 0(%r16)
	mulhdu %r22, %r19, %r0
	mulld %r0, %r19, %r0
	addc %r3, %r3, %r0
	subfe %r11, %r11, %r11
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	cmpldi %cr0, %r9, 0
	beq %cr0, 2149f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2151f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 2153f
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	addi %r14, %r14, 24
	addi %r15, %r15, 24
	addi %r16, %r16, 24
	b 2154f
2153:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	addi %r14, %r14, 16
	addi %r15, %r15, 16
	addi %r16, %r16, 16
2154:
	b 2152f
2151:
	ld %r3, 8(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	addze %r22, %r9
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
2152:
	b 2150f
2149:
2150:
	cmplwi %cr0, %r17, 0
	beq %cr0, 2155f
2157:
	ld %r3, 8(%r14)
	ld %r4, 16(%r14)
	ld %r7, 24(%r14)
	ld %r8, 32(%r14)
	subfc %r12, %r12, %r10
	ld %r9, 0(%r15)
	mulld %r0, %r18, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r15)
	mulld %r0, %r18, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r15)
	mulld %r0, %r18, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r15)
	mulld %r0, %r18, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r18, %r9
	subfe %r12, %r12, %r12
	addc %r3, %r3, %r20
	ld %r0, 0(%r15)
	mulhdu %r0, %r18, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r15)
	mulhdu %r0, %r18, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r15)
	mulhdu %r0, %r18, %r0
	adde %r8, %r8, %r0
	addze %r20, %r9
	subfc %r11, %r11, %r10
	ld %r9, 0(%r16)
	mulld %r0, %r19, %r9
	adde %r3, %r3, %r0
	ld %r9, 8(%r16)
	mulld %r0, %r19, %r9
	adde %r4, %r4, %r0
	ld %r9, 16(%r16)
	mulld %r0, %r19, %r9
	adde %r7, %r7, %r0
	ld %r9, 24(%r16)
	mulld %r0, %r19, %r9
	adde %r8, %r8, %r0
	mulhdu %r9, %r19, %r9
	subfe %r11, %r11, %r11
	addc %r3, %r3, %r22
	ld %r0, 0(%r16)
	mulhdu %r0, %r19, %r0
	adde %r4, %r4, %r0
	ld %r0, 8(%r16)
	mulhdu %r0, %r19, %r0
	adde %r7, %r7, %r0
	ld %r0, 16(%r16)
	mulhdu %r0, %r19, %r0
	adde %r8, %r8, %r0
	addze %r22, %r9
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	std %r7, 16(%r14)
	std %r8, 24(%r14)
	addi %r14, %r14, 32
	addi %r15, %r15, 32
	addi %r16, %r16, 32
	addi %r17, %r17, -1
	cmplwi %cr0, %r17, 0
	bne %cr0, 2157b
	b 2156f
2155:
2156:
	ld %r3, 8(%r14)
	li %r4, 0
	subfc %r12, %r12, %r10
	adde %r3, %r3, %r20
	addze %r4, %r4
	subfc %r11, %r11, %r10
	adde %r3, %r3, %r22
	addze %r4, %r4
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r9, 1
	rldicr %r9, %r9, 32, 31
	subf %r17, %r9, %r17
	rldicl %r9, %r17, 32, 32
	cmpldi %cr0, %r9, 0
	bne %cr0, 2148b
	subf %r3, %r10, %r16
	rldicl %r11, %r3, 62, 2
	subf %r7, %r3, %r15
	add %r8, %r3, %r3
	add %r8, %r8, %r10
	addi %r8, %r8, 32
	add %r9, %r8, %r3
	addi %r9, %r9, 16
	add %r4, %r8, %r3
	ld %r22, 8(%r4)
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2158:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2158b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2159:
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
	bne %cr0, 2159b
	addi %r24, %r24, -1
	cmpldi %cr0, %r24, 0
	bne %cr0, 2146b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2160:
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
	bne %cr0, 2160b
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
2161:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2161b
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
2162:
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
	bne %cr0, 2162b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r31, 256
	addi %r8, %r10, 0
	add %r8, %r8, %r29
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
2163:
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
	bne %cr0, 2163b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r31, 256
	rldicr %r12, %r2, 48, 15
	rldicl %r12, %r12, 16, 48
	li %r0, 28
	mulld %r12, %r12, %r0
	addi %r12, %r12, 704
	add %r12, %r12, %r21
	addi %r12, %r12, 1600
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2164:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2164b
	addi %r12, %r28, 0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	add %r12, %r12, %r6
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2165:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2165b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2166:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2166b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2167:
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
	bne %cr0, 2167b
	rldicr %r12, %r2, 48, 15
	rldicl %r12, %r12, 16, 48
	li %r0, 28
	mulld %r12, %r12, %r0
	addi %r12, %r12, 704
	add %r12, %r12, %r21
	addi %r12, %r12, 1600
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r30, %r12, 0
	addi %r31, %r6, 0
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
2168:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2168b
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
2169:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
	li %r25, 8
2170:
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
	addi %r7, %r10, 0
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r6, %r10, 0
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
	rldicl %r0, %r24, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	rldicr %r24, %r24, 1, 62
	addi %r8, %r10, 0
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
	addi %r17, %r11, 0
2171:
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
	bne %cr0, 2171b
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 2170b
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2169b
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
	rldicr %r6, %r2, 16, 47
	rldicl %r6, %r6, 16, 48
	rldicl %r0, %r2, 16, 48
	subf %r3, %r0, %r6
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	beq %cr0, 2172f
	b 2173f
2172:
	or %r6, %r0, %r0
2173:
	addi %r12, %r26, 0
	cmpldi %cr0, %r6, 0
	beq %cr0, 2174f
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2176:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2176b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2177:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2177b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	b 2175f
2174:
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2178:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2178b
2175:
	addi %r12, %r28, 0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2179:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2179b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2180:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2180b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
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
	mflr %r14
	addi %r3, %r12, 0
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
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	rldicr %r12, %r2, 48, 15
	rldicl %r12, %r12, 16, 48
	li %r0, 28
	mulld %r12, %r12, %r0
	addi %r12, %r12, 704
	add %r12, %r12, %r21
	addi %r12, %r12, 1600
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2182:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2182b
	rldicr %r12, %r2, 48, 15
	rldicl %r12, %r12, 16, 48
	li %r0, 28
	mulld %r12, %r12, %r0
	addi %r12, %r12, 704
	add %r12, %r12, %r21
	addi %r12, %r12, 1600
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	add %r12, %r12, %r6
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2183:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2183b
	addi %r23, %r21, 0
	addi %r31, %r21, 0
	addi %r10, %r21, 256
	rldicr %r11, %r2, 48, 15
	rldicl %r11, %r11, 16, 48
	rldicl %r11, %r11, 61, 3
	rldicr %r29, %r11, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r11, 1, 62
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r6
	add %r12, %r12, %r0
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2184:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2184b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2185:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2185b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	rldicr %r0, %r2, 32, 31
	rldicl %r0, %r0, 16, 48
	add %r12, %r27, %r6
	add %r12, %r12, %r0
	add %r12, %r12, %r6
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2186:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2186b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2187:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2187b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2188:
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
	bne %cr0, 2188b
	rldicr %r12, %r2, 48, 15
	rldicl %r12, %r12, 16, 48
	li %r0, 28
	mulld %r12, %r12, %r0
	addi %r12, %r12, 704
	add %r12, %r12, %r21
	addi %r12, %r12, 1600
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r30, %r12, 0
	add %r25, %r12, %r6
	addi %r31, %r6, 0
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
2189:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2189b
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
	add %r6, %r6, %r29
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
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2190:
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
	bne %cr0, 2190b
2191:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	lbz %r0, 0(%r25)
	rldicr %r0, %r0, 48, 15
	add %r24, %r24, %r0
	addi %r30, %r30, 1
	addi %r25, %r25, 1
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
	rldicl %r18, %r24, 2, 62
	rldicr %r3, %r24, 8, 55
	rldicl %r3, %r3, 2, 62
	rldicr %r3, %r3, 2, 61
	add %r18, %r18, %r3
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2192f
2194:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2194b
	b 2193f
2192:
2193:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2195f
2197:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2197b
	b 2196f
2195:
2196:
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
	rldicr %r24, %r24, 2, 61
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
	rldicl %r18, %r24, 2, 62
	rldicr %r3, %r24, 8, 55
	rldicl %r3, %r3, 2, 62
	rldicr %r3, %r3, 2, 61
	add %r18, %r18, %r3
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2198f
2200:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2200b
	b 2199f
2198:
2199:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2201f
2203:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2203b
	b 2202f
2201:
2202:
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
	rldicr %r24, %r24, 2, 61
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
	rldicl %r18, %r24, 2, 62
	rldicr %r3, %r24, 8, 55
	rldicl %r3, %r3, 2, 62
	rldicr %r3, %r3, 2, 61
	add %r18, %r18, %r3
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2204f
2206:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2206b
	b 2205f
2204:
2205:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2207f
2209:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2209b
	b 2208f
2207:
2208:
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
	rldicr %r24, %r24, 2, 61
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
	rldicl %r18, %r24, 2, 62
	rldicr %r3, %r24, 8, 55
	rldicl %r3, %r3, 2, 62
	rldicr %r3, %r3, 2, 61
	add %r18, %r18, %r3
	rldicl %r4, %r11, 61, 3
	rldicl %r0, %r11, 63, 1
	li %r9, 3
	and %r9, %r0, %r9
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	cmpldi %cr0, %r4, 0
	beq %cr0, 2210f
2212:
	li %r14, 0
	addi %r14, %r14, -1
	li %r15, 0
	addi %r15, %r15, -1
	li %r16, 0
	addi %r16, %r16, -1
	li %r17, 0
	addi %r17, %r17, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	ld %r0, 8(%r8)
	or %r0, %r0, %r20
	and %r15, %r15, %r0
	ld %r0, 16(%r8)
	or %r0, %r0, %r20
	and %r16, %r16, %r0
	ld %r0, 24(%r8)
	or %r0, %r0, %r20
	and %r17, %r17, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	std %r15, 8(%r5)
	std %r16, 16(%r5)
	std %r17, 24(%r5)
	addi %r5, %r5, 32
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2212b
	b 2211f
2210:
2211:
	cmpldi %cr0, %r9, 0
	beq %cr0, 2213f
2215:
	li %r14, 0
	addi %r14, %r14, -1
	li %r19, 0
	add %r8, %r5, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	addi %r20, %r3, -1
	ld %r0, 0(%r8)
	or %r0, %r0, %r20
	and %r14, %r14, %r0
	add %r8, %r8, %r29
	addi %r19, %r19, 1
	std %r14, 0(%r5)
	addi %r5, %r5, 8
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 2215b
	b 2214f
2213:
2214:
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
	rldicr %r24, %r24, 2, 61
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2191b
	addi %r31, %r23, 0
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
	rldicr %r12, %r2, 48, 15
	rldicl %r12, %r12, 16, 48
	li %r0, 28
	mulld %r12, %r12, %r0
	addi %r12, %r12, 704
	add %r12, %r12, %r21
	addi %r12, %r12, 1600
	rldicr %r6, %r2, 48, 15
	rldicl %r6, %r6, 16, 48
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2216:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2216b
	li %r20, 0
	addi %r20, %r20, -1
	addi %r8, %r10, 0
	add %r8, %r8, %r29
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
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2217:
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
	bne %cr0, 2217b
	rldicr %r23, %r2, 48, 15
	rldicl %r23, %r23, 16, 48
	li %r11, 28
	mulld %r23, %r23, %r11
	addi %r23, %r23, 704
	add %r23, %r23, %r21
	addi %r31, %r23, 0
	addi %r10, %r23, 256
	li %r11, 8
	li %r29, 48
	rldicr %r30, %r2, 48, 15
	rldicl %r30, %r30, 16, 48
	addi %r30, %r30, 16
	li %r0, 6
	mulld %r30, %r30, %r0
	add %r30, %r30, %r21
	addi %r30, %r30, 256
	rldicr %r31, %r2, 48, 15
	rldicl %r31, %r31, 16, 48
	rldicl %r31, %r31, 61, 3
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
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	rldicl %r17, %r11, 63, 1
2218:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2218b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	ld %r3, 0(%r14)
	addi %r3, %r3, -1
	std %r3, 0(%r14)
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
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
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2219:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2219b
2220:
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r30, 0
	rldicl %r17, %r11, 63, 1
2221:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2221b
	addi %r30, %r15, 0
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
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
	mflr %r14
	addi %r3, %r12, 0
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
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
2222:
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
	bne %cr0, 2222b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r23, 256
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r24, 0
2223:
	lwz %r0, 0(%r15)
	lwz %r3, 0(%r16)
	and %r3, %r3, %r20
	add %r0, %r0, %r3
	add %r0, %r0, %r24
	stw %r0, 0(%r15)
	rldicl %r24, %r0, 32, 32
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2223b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
2224:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2224b
	rldicl %r3, %r11, 63, 1
	subf %r31, %r3, %r31
	addi %r3, %r31, -1
	rldicl %r3, %r3, 1, 63
	li %r0, 1
	xor %r3, %r3, %r0
	cmpldi %cr0, %r3, 0
	bne %cr0, 2220b
	addi %r31, %r23, 0
	addi %r12, %r28, 0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2225:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2225b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2226:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2226b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2227:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2227b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r3, %r3, %r0
	ld %r4, 0(%r21)
	and %r3, %r3, %r4
	li %r0, 1
	and %r3, %r3, %r0
221:
29:
24:
	ld %r14, 104(%r21)
	ld %r15, 112(%r21)
	ld %r16, 120(%r21)
	ld %r17, 128(%r21)
	ld %r18, 136(%r21)
	ld %r19, 144(%r21)
	ld %r20, 152(%r21)
	ld %r22, 160(%r21)
	ld %r23, 168(%r21)
	ld %r24, 176(%r21)
	ld %r25, 184(%r21)
	ld %r26, 192(%r21)
	ld %r27, 200(%r21)
	ld %r28, 208(%r21)
	ld %r29, 216(%r21)
	ld %r30, 224(%r21)
	ld %r31, 232(%r21)
	ld %r2, 240(%r21)
	ld %r21, 248(%r21)
	blr

vg_dsa_parameter_search_init:
	addi %r0, %r4, -128
	cmpldi %cr0, %r0, 0
	beq %cr0, 20f
	addi %r0, %r4, -256
	cmpldi %cr0, %r0, 0
	beq %cr0, 22f
	addi %r0, %r4, -384
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	li %r5, 0
	std %r5, 0(%r3)
	std %r5, 8(%r3)
	std %r5, 16(%r3)
	std %r5, 24(%r3)
	li %r3, 0
	b 25f
24:
	li %r5, 4096
	std %r5, 0(%r3)
	std %r4, 8(%r3)
	rldicr %r5, %r4, 15, 48
	add %r5, %r5, %r4
	std %r5, 16(%r3)
	rldicr %r5, %r4, 9, 54
	std %r5, 24(%r3)
	li %r3, 1
25:
	b 23f
22:
	li %r5, 4096
	std %r5, 0(%r3)
	std %r4, 8(%r3)
	rldicr %r5, %r4, 15, 48
	add %r5, %r5, %r4
	std %r5, 16(%r3)
	rldicr %r5, %r4, 9, 54
	std %r5, 24(%r3)
	li %r3, 1
23:
	b 21f
20:
	li %r5, 4096
	std %r5, 0(%r3)
	std %r4, 8(%r3)
	rldicr %r5, %r4, 15, 48
	add %r5, %r5, %r4
	std %r5, 16(%r3)
	rldicr %r5, %r4, 9, 54
	std %r5, 24(%r3)
	li %r3, 1
21:
	blr

vg_dsa_parameter_search:
	mflr %r0
	ld %r11, 0(%r10)
	ld %r12, 8(%r10)
	li %r4, 0
	std %r0, 120(%r8)
	std %r2, 200(%r8)
	std %r14, 208(%r8)
	std %r15, 216(%r8)
	std %r16, 224(%r8)
	std %r17, 232(%r8)
	std %r18, 240(%r8)
	std %r19, 248(%r8)
	std %r20, 256(%r8)
	std %r21, 264(%r8)
	std %r22, 272(%r8)
	std %r23, 280(%r8)
	std %r24, 288(%r8)
	std %r25, 296(%r8)
	std %r26, 304(%r8)
	std %r27, 312(%r8)
	std %r29, 320(%r8)
	std %r30, 328(%r8)
	std %r31, 336(%r8)
	std %r28, 344(%r8)
	std %r3, 0(%r8)
	std %r5, 144(%r8)
	std %r6, 72(%r8)
	std %r7, 80(%r8)
	std %r10, 152(%r8)
	std %r11, 16(%r8)
	std %r4, 160(%r8)
	std %r4, 64(%r8)
	addi %r28, %r8, 0
	addi %r0, %r12, -128
	cmpldi %cr0, %r0, 0
	beq %cr0, 20f
	addi %r0, %r12, -256
	cmpldi %cr0, %r0, 0
	beq %cr0, 22f
	li %r0, 0
	std %r0, 512(%r28)
	std %r0, 520(%r28)
	std %r0, 528(%r28)
	std %r0, 536(%r28)
	std %r0, 544(%r28)
	std %r0, 552(%r28)
	std %r0, 560(%r28)
	std %r0, 568(%r28)
	li %r0, 128
	stb %r0, 544(%r28)
	li %r0, 1
	stb %r0, 574(%r28)
	li %r0, 0
	stb %r0, 575(%r28)
24:
	ld %r3, 16(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 25f
	ld %r3, 80(%r28)
	ld %r4, 160(%r28)
	subf %r3, %r4, %r3
	li %r4, 32
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 27f
	ld %r3, 72(%r28)
	ld %r4, 160(%r28)
	add %r3, %r3, %r4
	std %r3, 8(%r28)
	addi %r4, %r4, 32
	std %r4, 24(%r28)
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
29:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 29b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 20608
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 608
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -608
	lbz %r0, 608(%r28)
	ori %r0, %r0, 128
	stb %r0, 608(%r28)
	lbz %r0, 639(%r28)
	ori %r0, %r0, 1
	stb %r0, 639(%r28)
	addi %r3, %r28, 608
	addi %r4, %r28, 20608
	li %r5, 32
210:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	addi %r3, %r28, 20608
	li %r4, 23024
	ld %r9, 24(%r28)
	ld %r5, 72(%r28)
	ld %r6, 80(%r28)
	add %r5, %r5, %r9
	subf %r6, %r9, %r6
	addi %r7, %r28, 112
	cmpldi %cr0, %r6, 0
	beq %cr0, 211f
	b 212f
211:
	ld %r5, 72(%r28)
212:
	bl {vg_dsa_probable_prime_256}
	rlwinm %r3, %r3, 0, 0, 31
	std %r3, 88(%r28)
	cmpldi %cr0, %r3, 0
	beq %cr0, 213f
	ld %r4, 112(%r28)
	ld %r5, 24(%r28)
	add %r5, %r5, %r4
	std %r5, 24(%r28)
	b 214f
213:
214:
	ld %r3, 88(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 215f
	ld %r3, 88(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 217f
	b 218f
217:
	li %r3, 0
	std %r3, 32(%r28)
	li %r3, 1
	std %r3, 40(%r28)
	li %r3, 4
	std %r3, 96(%r28)
219:
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
220:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 0
	li %r6, 32
221:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 221b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 20608
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 1024
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -1024
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
222:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 222b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 1
	li %r6, 32
223:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 223b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 20608
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 992
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -992
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
224:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 224b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 2
	li %r6, 32
225:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 225b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 20608
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 960
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -960
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
226:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 226b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 3
	li %r6, 32
227:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 227b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 20608
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 928
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -928
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
228:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 228b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 4
	li %r6, 32
229:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 229b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 20608
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 896
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -896
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
230:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 230b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 5
	li %r6, 32
231:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 231b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 20608
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 864
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -864
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
232:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 232b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 6
	li %r6, 32
233:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 233b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 20608
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 832
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -832
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
234:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 234b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 7
	li %r6, 32
235:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 235b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 20608
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 800
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -800
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
236:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 236b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 8
	li %r6, 32
237:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 237b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 20608
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 768
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -768
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
238:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 238b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 9
	li %r6, 32
239:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 239b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 20608
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 736
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -736
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
240:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 240b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 10
	li %r6, 32
241:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 241b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 20608
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 704
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -704
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
242:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 242b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 11
	li %r6, 32
243:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 243b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 20608
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 672
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -672
	lbz %r0, 672(%r28)
	ori %r0, %r0, 128
	stb %r0, 672(%r28)
	addi %r31, %r28, 14528
	li %r29, 96
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r8, 15
	mulld %r8, %r8, %r30
	rldicl %r8, %r8, 62, 2
	addi %r5, %r31, 160
	li %r0, 0
244:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 244b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	addi %r6, %r28, 672
	li %r8, 384
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
245:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 245b
	addi %r6, %r28, 672
	li %r8, 384
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
246:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 246b
	addi %r6, %r28, 608
	li %r8, 32
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
247:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 247b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
248:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 248b
	rldicr %r4, %r29, 5, 58
249:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 250f
	addi %r8, %r29, 0
252:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 252b
	b 251f
250:
	rldicl %r8, %r29, 63, 1
253:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 253b
251:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 254f
	addi %r8, %r29, 1
256:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 256b
	b 255f
254:
	rldicl %r8, %r29, 63, 1
257:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 257b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
255:
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 258f
	addi %r8, %r29, 1
	li %r9, 0
260:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 260b
	b 259f
258:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
261:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 261b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
259:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 3
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 262f
	addi %r8, %r29, 1
264:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 264b
	b 263f
262:
	rldicl %r8, %r29, 63, 1
265:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 265b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
263:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 249b
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 266f
	addi %r8, %r29, 0
	li %r9, 0
268:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 268b
	b 267f
266:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
269:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 269b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
267:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 136(%r31)
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 136(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 270f
	addi %r8, %r29, 0
272:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 272b
	b 271f
270:
	rldicl %r8, %r29, 63, 1
273:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 273b
271:
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 274f
	addi %r8, %r29, 0
	li %r9, 0
276:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 276b
	b 275f
274:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
277:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 277b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
275:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 278f
	addi %r8, %r29, 0
280:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 280b
	b 279f
278:
	rldicl %r8, %r29, 63, 1
281:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 281b
279:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 282f
	addi %r8, %r29, 0
284:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 284b
	b 283f
282:
	rldicl %r8, %r29, 63, 1
285:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 285b
283:
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	addi %r5, %r28, 1056
	li %r8, 384
	li %r9, 0
	addi %r9, %r9, -1
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
286:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 286b
	addi %r5, %r28, 1440
	li %r8, 353
	li %r9, 0
	addi %r9, %r9, -1
	li %r6, 9
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
287:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 287b
	lbz %r0, 1056(%r28)
	rldicl %r0, %r0, 57, 7
	cmpldi %cr0, %r0, 0
	beq %cr0, 288f
	addi %r3, %r28, 1056
	addi %r4, %r28, 20608
	li %r5, 384
290:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 290b
	addi %r3, %r28, 20608
	li %r4, 23024
	ld %r9, 24(%r28)
	ld %r5, 72(%r28)
	ld %r6, 80(%r28)
	add %r5, %r5, %r9
	subf %r6, %r9, %r6
	addi %r7, %r28, 112
	cmpldi %cr0, %r6, 0
	beq %cr0, 291f
	b 292f
291:
	ld %r5, 72(%r28)
292:
	bl {vg_dsa_probable_prime_3072}
	rlwinm %r3, %r3, 0, 0, 31
	std %r3, 88(%r28)
	cmpldi %cr0, %r3, 0
	beq %cr0, 293f
	ld %r4, 112(%r28)
	ld %r5, 24(%r28)
	add %r5, %r5, %r4
	std %r5, 24(%r28)
	b 294f
293:
294:
	ld %r3, 88(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 295f
	ld %r3, 88(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 297f
	b 298f
297:
	li %r3, 1
	std %r3, 96(%r28)
298:
	b 296f
295:
	li %r3, 0
	std %r3, 96(%r28)
296:
	b 289f
288:
289:
	ld %r3, 96(%r28)
	addi %r0, %r3, -4
	cmpldi %cr0, %r0, 0
	beq %cr0, 299f
	b 2100f
299:
	ld %r3, 32(%r28)
	addi %r3, %r3, 1
	std %r3, 32(%r28)
	ld %r4, 40(%r28)
	addi %r4, %r4, 12
	std %r4, 40(%r28)
	addi %r0, %r3, -12288
	cmpldi %cr0, %r0, 0
	beq %cr0, 2101f
	b 2102f
2101:
	li %r3, 2
	std %r3, 96(%r28)
2102:
2100:
	ld %r3, 96(%r28)
	addi %r0, %r3, -4
	cmpldi %cr0, %r0, 0
	beq %cr0, 219b
	ld %r3, 96(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2103f
	ld %r3, 96(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2105f
	b 2106f
2105:
	ld %r3, 72(%r28)
	ld %r4, 24(%r28)
	add %r3, %r3, %r4
	std %r3, 128(%r28)
	ld %r3, 80(%r28)
	subf %r3, %r4, %r3
	li %r4, 384
	rldicr %r4, %r4, 7, 56
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2107f
	std %r4, 136(%r28)
	b 2108f
2107:
	std %r3, 136(%r28)
2108:
	ld %r3, 128(%r28)
	std %r3, 48(%r28)
	ld %r3, 136(%r28)
	std %r3, 56(%r28)
	li %r3, 4
	std %r3, 104(%r28)
2109:
	ld %r3, 56(%r28)
	li %r4, 384
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2110f
	addi %r31, %r28, 14528
	li %r29, 96
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2112f
	addi %r8, %r29, 0
2114:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2114b
	b 2113f
2112:
	rldicl %r8, %r29, 63, 1
2115:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2115b
2113:
	ld %r6, 48(%r28)
	li %r8, 384
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
2116:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2116b
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 10
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2117f
	addi %r8, %r29, 0
	li %r9, 0
2119:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2119b
	b 2118f
2117:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2120:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2120b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2118:
	stw %r9, 140(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2121f
	addi %r8, %r29, 0
	li %r9, 0
2123:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2123b
	b 2122f
2121:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2124:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2124b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2122:
	stw %r9, 144(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 144(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	lwz %r0, 140(%r31)
	cmpldi %cr0, %r0, 0
	beq %cr0, 2125f
	addi %r21, %r28, 3072
	addi %r23, %r21, 0
	addi %r31, %r21, 0
	addi %r10, %r21, 256
	li %r11, 96
	li %r29, 400
	addi %r12, %r28, 1056
	li %r6, 384
	addi %r10, %r10, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2127:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2127b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2128:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2128b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2129:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2129b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 6, 57
2130:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
2131:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2131b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2132:
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
	bne %cr0, 2132b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
2133:
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
	bne %cr0, 2133b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2130b
	ld %r12, 48(%r28)
	li %r6, 384
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2134:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2134b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2135:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2135b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
	addi %r30, %r28, 1440
	li %r31, 353
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
2136:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2136b
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
2137:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
	li %r25, 8
2138:
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
	addi %r7, %r10, 0
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r6, %r10, 0
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
	rldicl %r0, %r24, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	rldicr %r24, %r24, 1, 62
	addi %r8, %r10, 0
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
	addi %r17, %r11, 0
2139:
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
	bne %cr0, 2139b
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 2138b
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2137b
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
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2140:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2140b
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
	addi %r10, %r31, 256
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2141:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2141b
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2142:
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
	bne %cr0, 2142b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
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
2143:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2143b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
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
2144:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2144b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	addi %r3, %r20, 0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2145f
	b 2146f
2145:
	addi %r12, %r28, 1824
	li %r6, 384
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2147:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2147b
	li %r3, 1
	std %r3, 104(%r28)
2146:
	b 2126f
2125:
2126:
	ld %r3, 48(%r28)
	addi %r3, %r3, 384
	std %r3, 48(%r28)
	ld %r3, 56(%r28)
	addi %r3, %r3, -384
	std %r3, 56(%r28)
	b 2111f
2110:
	li %r3, 2
	std %r3, 104(%r28)
2111:
	ld %r3, 104(%r28)
	addi %r0, %r3, -4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2109b
	ld %r3, 48(%r28)
	ld %r4, 72(%r28)
	subf %r3, %r4, %r3
	std %r3, 24(%r28)
	ld %r3, 104(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2148f
	ld %r3, 136(%r28)
	li %r4, 384
	rldicr %r4, %r4, 7, 56
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2150f
	b 2151f
2150:
	li %r3, 2
	std %r3, 64(%r28)
2151:
	b 2149f
2148:
	addi %r3, %r28, 1056
	addi %r4, %r28, 2208
	li %r5, 384
2152:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2152b
	addi %r3, %r28, 608
	addi %r4, %r28, 2592
	li %r5, 32
2153:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2153b
	addi %r3, %r28, 1824
	addi %r4, %r28, 2624
	li %r5, 384
2154:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2154b
	addi %r3, %r28, 2208
	li %r4, 800
	li %r5, 384
	li %r6, 32
	addi %r7, %r28, 20608
	li %r8, 23024
	bl {vg_dsa_check_parameters}
	rlwinm %r3, %r3, 0, 0, 31
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2155f
	b 2156f
2155:
	li %r3, 1
	std %r3, 64(%r28)
2156:
2149:
2106:
	b 2104f
2103:
	li %r3, 2
	std %r3, 64(%r28)
2104:
218:
	b 216f
215:
	li %r3, 2
	std %r3, 64(%r28)
216:
	ld %r3, 64(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2157f
	b 2158f
2157:
	ld %r3, 24(%r28)
	std %r3, 160(%r28)
	ld %r3, 16(%r28)
	addi %r3, %r3, -1
	std %r3, 16(%r28)
2158:
	b 28f
27:
	li %r3, 2
	std %r3, 64(%r28)
28:
	b 26f
25:
	li %r3, 3
	std %r3, 64(%r28)
26:
	ld %r3, 64(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 24b
	ld %r3, 64(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2159f
	ld %r3, 64(%r28)
	addi %r0, %r3, -2
	cmpldi %cr0, %r0, 0
	beq %cr0, 2161f
	li %r5, 0
	li %r6, 0
	ld %r3, 160(%r28)
	std %r3, 168(%r28)
	li %r3, 3
	std %r3, 192(%r28)
	std %r5, 176(%r28)
	std %r6, 184(%r28)
	b 2162f
2161:
	ld %r3, 80(%r28)
	ld %r4, 160(%r28)
	subf %r3, %r4, %r3
	li %r4, 384
	rldicr %r5, %r4, 15, 48
	add %r4, %r4, %r5
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2163f
	li %r5, 0
	li %r6, 0
	ld %r3, 160(%r28)
	std %r3, 168(%r28)
	li %r3, 3
	std %r3, 192(%r28)
	std %r5, 176(%r28)
	std %r6, 184(%r28)
	b 2164f
2163:
	li %r4, 384
	rldicr %r4, %r4, 8, 55
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2165f
	b 2166f
2165:
	addi %r3, %r4, 0
2166:
	add %r3, %r3, %r3
	li %r4, 384
	rldicr %r5, %r4, 15, 48
	add %r4, %r4, %r5
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2167f
	addi %r3, %r4, 0
	b 2168f
2167:
2168:
	addi %r6, %r3, 0
	ld %r5, 16(%r28)
	ld %r3, 160(%r28)
	std %r3, 168(%r28)
	li %r3, 0
	std %r3, 192(%r28)
	std %r5, 176(%r28)
	std %r6, 184(%r28)
2164:
2162:
	b 2160f
2159:
	li %r5, 0
	li %r6, 0
	ld %r3, 24(%r28)
	std %r3, 168(%r28)
	li %r3, 1
	std %r3, 192(%r28)
	std %r5, 176(%r28)
	std %r6, 184(%r28)
2160:
	ld %r3, 64(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2169f
	ld %r3, 0(%r28)
	li %r5, 800
	li %r0, 0
2171:
	stb %r0, 0(%r3)
	addi %r3, %r3, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2171b
	b 2170f
2169:
	addi %r3, %r28, 2208
	ld %r4, 0(%r28)
	li %r5, 800
2172:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2172b
2170:
	ld %r3, 152(%r28)
	ld %r4, 176(%r28)
	std %r4, 0(%r3)
	ld %r4, 184(%r28)
	std %r4, 24(%r3)
	ld %r3, 144(%r28)
	ld %r4, 168(%r28)
	std %r4, 0(%r3)
	ld %r3, 192(%r28)
	b 23f
22:
	li %r0, 0
	std %r0, 512(%r28)
	std %r0, 520(%r28)
	std %r0, 528(%r28)
	std %r0, 536(%r28)
	std %r0, 544(%r28)
	std %r0, 552(%r28)
	std %r0, 560(%r28)
	std %r0, 568(%r28)
	li %r0, 128
	stb %r0, 544(%r28)
	li %r0, 1
	stb %r0, 574(%r28)
	li %r0, 0
	stb %r0, 575(%r28)
2173:
	ld %r3, 16(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2174f
	ld %r3, 80(%r28)
	ld %r4, 160(%r28)
	subf %r3, %r4, %r3
	li %r4, 32
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2176f
	ld %r3, 72(%r28)
	ld %r4, 160(%r28)
	add %r3, %r3, %r4
	std %r3, 8(%r28)
	addi %r4, %r4, 32
	std %r4, 24(%r28)
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
2178:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2178b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 15104
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 608
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -608
	lbz %r0, 608(%r28)
	ori %r0, %r0, 128
	stb %r0, 608(%r28)
	lbz %r0, 639(%r28)
	ori %r0, %r0, 1
	stb %r0, 639(%r28)
	addi %r3, %r28, 608
	addi %r4, %r28, 15104
	li %r5, 32
2179:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2179b
	addi %r3, %r28, 15104
	li %r4, 15520
	ld %r9, 24(%r28)
	ld %r5, 72(%r28)
	ld %r6, 80(%r28)
	add %r5, %r5, %r9
	subf %r6, %r9, %r6
	addi %r7, %r28, 112
	cmpldi %cr0, %r6, 0
	beq %cr0, 2180f
	b 2181f
2180:
	ld %r5, 72(%r28)
2181:
	bl {vg_dsa_probable_prime_256}
	rlwinm %r3, %r3, 0, 0, 31
	std %r3, 88(%r28)
	cmpldi %cr0, %r3, 0
	beq %cr0, 2182f
	ld %r4, 112(%r28)
	ld %r5, 24(%r28)
	add %r5, %r5, %r4
	std %r5, 24(%r28)
	b 2183f
2182:
2183:
	ld %r3, 88(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2184f
	ld %r3, 88(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2186f
	b 2187f
2186:
	li %r3, 0
	std %r3, 32(%r28)
	li %r3, 1
	std %r3, 40(%r28)
	li %r3, 4
	std %r3, 96(%r28)
2188:
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
2189:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2189b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 0
	li %r6, 32
2190:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2190b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 15104
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 896
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -896
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
2191:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2191b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 1
	li %r6, 32
2192:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2192b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 15104
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 864
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -864
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
2193:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2193b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 2
	li %r6, 32
2194:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2194b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 15104
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 832
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -832
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
2195:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2195b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 3
	li %r6, 32
2196:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2196b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 15104
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 800
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -800
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
2197:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2197b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 4
	li %r6, 32
2198:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2198b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 15104
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 768
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -768
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
2199:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2199b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 5
	li %r6, 32
2200:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2200b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 15104
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 736
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -736
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
2201:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2201b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 6
	li %r6, 32
2202:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2202b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 15104
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 704
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -704
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 32
2203:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2203b
	addi %r3, %r28, 543
	ld %r4, 40(%r28)
	addi %r4, %r4, 7
	li %r6, 32
2204:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2204b
	lis %r0, 27145
	ori %r0, %r0, 58983
	stw %r0, 576(%r28)
	lis %r0, -17561
	ori %r0, %r0, 44677
	stw %r0, 580(%r28)
	lis %r0, 15470
	ori %r0, %r0, 62322
	stw %r0, 584(%r28)
	lis %r0, -23217
	ori %r0, %r0, 62778
	stw %r0, 588(%r28)
	lis %r0, 20750
	ori %r0, %r0, 21119
	stw %r0, 592(%r28)
	lis %r0, -25851
	ori %r0, %r0, 26764
	stw %r0, 596(%r28)
	lis %r0, 8067
	ori %r0, %r0, 55723
	stw %r0, 600(%r28)
	lis %r0, 23520
	ori %r0, %r0, 52505
	stw %r0, 604(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 15104
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha256_compress}
	addi %r28, %r28, 672
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	lwz %r8, 20(%r26)
	li %r11, 20
	stwbrx %r8, %r28, %r11
	lwz %r8, 24(%r26)
	li %r11, 24
	stwbrx %r8, %r28, %r11
	lwz %r8, 28(%r26)
	li %r11, 28
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -672
	lbz %r0, 672(%r28)
	ori %r0, %r0, 128
	stb %r0, 672(%r28)
	addi %r31, %r28, 10944
	li %r29, 64
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r8, 15
	mulld %r8, %r8, %r30
	rldicl %r8, %r8, 62, 2
	addi %r5, %r31, 160
	li %r0, 0
2205:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2205b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	addi %r6, %r28, 672
	li %r8, 256
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
2206:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2206b
	addi %r6, %r28, 672
	li %r8, 256
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
2207:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2207b
	addi %r6, %r28, 608
	li %r8, 32
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
2208:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2208b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2209:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2209b
	rldicr %r4, %r29, 5, 58
2210:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2211f
	addi %r8, %r29, 0
2213:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2213b
	b 2212f
2211:
	rldicl %r8, %r29, 63, 1
2214:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2214b
2212:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2215f
	addi %r8, %r29, 1
2217:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2217b
	b 2216f
2215:
	rldicl %r8, %r29, 63, 1
2218:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2218b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2216:
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2219f
	addi %r8, %r29, 1
	li %r9, 0
2221:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2221b
	b 2220f
2219:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2222:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2222b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2220:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 3
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2223f
	addi %r8, %r29, 1
2225:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2225b
	b 2224f
2223:
	rldicl %r8, %r29, 63, 1
2226:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2226b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2224:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2210b
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2227f
	addi %r8, %r29, 0
	li %r9, 0
2229:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2229b
	b 2228f
2227:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2230:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2230b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2228:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 136(%r31)
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 136(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2231f
	addi %r8, %r29, 0
2233:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2233b
	b 2232f
2231:
	rldicl %r8, %r29, 63, 1
2234:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2234b
2232:
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2235f
	addi %r8, %r29, 0
	li %r9, 0
2237:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2237b
	b 2236f
2235:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2238:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2238b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2236:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2239f
	addi %r8, %r29, 0
2241:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2241b
	b 2240f
2239:
	rldicl %r8, %r29, 63, 1
2242:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2242b
2240:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2243f
	addi %r8, %r29, 0
2245:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2245b
	b 2244f
2243:
	rldicl %r8, %r29, 63, 1
2246:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2246b
2244:
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	addi %r5, %r28, 1056
	li %r8, 256
	li %r9, 0
	addi %r9, %r9, -1
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2247:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2247b
	addi %r5, %r28, 1440
	li %r8, 225
	li %r9, 0
	addi %r9, %r9, -1
	li %r6, 9
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2248:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2248b
	lbz %r0, 1056(%r28)
	rldicl %r0, %r0, 57, 7
	cmpldi %cr0, %r0, 0
	beq %cr0, 2249f
	addi %r3, %r28, 1056
	addi %r4, %r28, 15104
	li %r5, 256
2251:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2251b
	addi %r3, %r28, 15104
	li %r4, 15520
	ld %r9, 24(%r28)
	ld %r5, 72(%r28)
	ld %r6, 80(%r28)
	add %r5, %r5, %r9
	subf %r6, %r9, %r6
	addi %r7, %r28, 112
	cmpldi %cr0, %r6, 0
	beq %cr0, 2252f
	b 2253f
2252:
	ld %r5, 72(%r28)
2253:
	bl {vg_dsa_probable_prime_2048}
	rlwinm %r3, %r3, 0, 0, 31
	std %r3, 88(%r28)
	cmpldi %cr0, %r3, 0
	beq %cr0, 2254f
	ld %r4, 112(%r28)
	ld %r5, 24(%r28)
	add %r5, %r5, %r4
	std %r5, 24(%r28)
	b 2255f
2254:
2255:
	ld %r3, 88(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2256f
	ld %r3, 88(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2258f
	b 2259f
2258:
	li %r3, 1
	std %r3, 96(%r28)
2259:
	b 2257f
2256:
	li %r3, 0
	std %r3, 96(%r28)
2257:
	b 2250f
2249:
2250:
	ld %r3, 96(%r28)
	addi %r0, %r3, -4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2260f
	b 2261f
2260:
	ld %r3, 32(%r28)
	addi %r3, %r3, 1
	std %r3, 32(%r28)
	ld %r4, 40(%r28)
	addi %r4, %r4, 8
	std %r4, 40(%r28)
	addi %r0, %r3, -8192
	cmpldi %cr0, %r0, 0
	beq %cr0, 2262f
	b 2263f
2262:
	li %r3, 2
	std %r3, 96(%r28)
2263:
2261:
	ld %r3, 96(%r28)
	addi %r0, %r3, -4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2188b
	ld %r3, 96(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2264f
	ld %r3, 96(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2266f
	b 2267f
2266:
	ld %r3, 72(%r28)
	ld %r4, 24(%r28)
	add %r3, %r3, %r4
	std %r3, 128(%r28)
	ld %r3, 80(%r28)
	subf %r3, %r4, %r3
	li %r4, 256
	rldicr %r4, %r4, 7, 56
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2268f
	std %r4, 136(%r28)
	b 2269f
2268:
	std %r3, 136(%r28)
2269:
	ld %r3, 128(%r28)
	std %r3, 48(%r28)
	ld %r3, 136(%r28)
	std %r3, 56(%r28)
	li %r3, 4
	std %r3, 104(%r28)
2270:
	ld %r3, 56(%r28)
	li %r4, 256
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2271f
	addi %r31, %r28, 10944
	li %r29, 64
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2273f
	addi %r8, %r29, 0
2275:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2275b
	b 2274f
2273:
	rldicl %r8, %r29, 63, 1
2276:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2276b
2274:
	ld %r6, 48(%r28)
	li %r8, 256
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
2277:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2277b
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 10
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2278f
	addi %r8, %r29, 0
	li %r9, 0
2280:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2280b
	b 2279f
2278:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2281:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2281b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2279:
	stw %r9, 140(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2282f
	addi %r8, %r29, 0
	li %r9, 0
2284:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2284b
	b 2283f
2282:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2285:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2285b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2283:
	stw %r9, 144(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 144(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	lwz %r0, 140(%r31)
	cmpldi %cr0, %r0, 0
	beq %cr0, 2286f
	addi %r21, %r28, 3072
	addi %r23, %r21, 0
	addi %r31, %r21, 0
	addi %r10, %r21, 256
	li %r11, 64
	li %r29, 272
	addi %r12, %r28, 1056
	li %r6, 256
	addi %r10, %r10, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2288:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2288b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2289:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2289b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2290:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2290b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 6, 57
2291:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
2292:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2292b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2293:
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
	bne %cr0, 2293b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
2294:
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
	bne %cr0, 2294b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2291b
	ld %r12, 48(%r28)
	li %r6, 256
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2295:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2295b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2296:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2296b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
	addi %r30, %r28, 1440
	li %r31, 225
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
2297:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2297b
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
2298:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
	li %r25, 8
2299:
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
	addi %r7, %r10, 0
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r6, %r10, 0
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
	rldicl %r0, %r24, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	rldicr %r24, %r24, 1, 62
	addi %r8, %r10, 0
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
	addi %r17, %r11, 0
2300:
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
	bne %cr0, 2300b
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 2299b
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2298b
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
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2301:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2301b
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
	addi %r10, %r31, 256
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2302:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2302b
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2303:
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
	bne %cr0, 2303b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
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
2304:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2304b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
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
2305:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2305b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	addi %r3, %r20, 0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2306f
	b 2307f
2306:
	addi %r12, %r28, 1824
	li %r6, 256
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2308:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2308b
	li %r3, 1
	std %r3, 104(%r28)
2307:
	b 2287f
2286:
2287:
	ld %r3, 48(%r28)
	addi %r3, %r3, 256
	std %r3, 48(%r28)
	ld %r3, 56(%r28)
	addi %r3, %r3, -256
	std %r3, 56(%r28)
	b 2272f
2271:
	li %r3, 2
	std %r3, 104(%r28)
2272:
	ld %r3, 104(%r28)
	addi %r0, %r3, -4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2270b
	ld %r3, 48(%r28)
	ld %r4, 72(%r28)
	subf %r3, %r4, %r3
	std %r3, 24(%r28)
	ld %r3, 104(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2309f
	ld %r3, 136(%r28)
	li %r4, 256
	rldicr %r4, %r4, 7, 56
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2311f
	b 2312f
2311:
	li %r3, 2
	std %r3, 64(%r28)
2312:
	b 2310f
2309:
	addi %r3, %r28, 1056
	addi %r4, %r28, 2208
	li %r5, 256
2313:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2313b
	addi %r3, %r28, 608
	addi %r4, %r28, 2464
	li %r5, 32
2314:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2314b
	addi %r3, %r28, 1824
	addi %r4, %r28, 2496
	li %r5, 256
2315:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2315b
	addi %r3, %r28, 2208
	li %r4, 544
	li %r5, 256
	li %r6, 32
	addi %r7, %r28, 15104
	li %r8, 15520
	bl {vg_dsa_check_parameters}
	rlwinm %r3, %r3, 0, 0, 31
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2316f
	b 2317f
2316:
	li %r3, 1
	std %r3, 64(%r28)
2317:
2310:
2267:
	b 2265f
2264:
	li %r3, 2
	std %r3, 64(%r28)
2265:
2187:
	b 2185f
2184:
	li %r3, 2
	std %r3, 64(%r28)
2185:
	ld %r3, 64(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2318f
	b 2319f
2318:
	ld %r3, 24(%r28)
	std %r3, 160(%r28)
	ld %r3, 16(%r28)
	addi %r3, %r3, -1
	std %r3, 16(%r28)
2319:
	b 2177f
2176:
	li %r3, 2
	std %r3, 64(%r28)
2177:
	b 2175f
2174:
	li %r3, 3
	std %r3, 64(%r28)
2175:
	ld %r3, 64(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2173b
	ld %r3, 64(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2320f
	ld %r3, 64(%r28)
	addi %r0, %r3, -2
	cmpldi %cr0, %r0, 0
	beq %cr0, 2322f
	li %r5, 0
	li %r6, 0
	ld %r3, 160(%r28)
	std %r3, 168(%r28)
	li %r3, 3
	std %r3, 192(%r28)
	std %r5, 176(%r28)
	std %r6, 184(%r28)
	b 2323f
2322:
	ld %r3, 80(%r28)
	ld %r4, 160(%r28)
	subf %r3, %r4, %r3
	li %r4, 256
	rldicr %r5, %r4, 15, 48
	add %r4, %r4, %r5
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2324f
	li %r5, 0
	li %r6, 0
	ld %r3, 160(%r28)
	std %r3, 168(%r28)
	li %r3, 3
	std %r3, 192(%r28)
	std %r5, 176(%r28)
	std %r6, 184(%r28)
	b 2325f
2324:
	li %r4, 256
	rldicr %r4, %r4, 8, 55
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2326f
	b 2327f
2326:
	addi %r3, %r4, 0
2327:
	add %r3, %r3, %r3
	li %r4, 256
	rldicr %r5, %r4, 15, 48
	add %r4, %r4, %r5
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2328f
	addi %r3, %r4, 0
	b 2329f
2328:
2329:
	addi %r6, %r3, 0
	ld %r5, 16(%r28)
	ld %r3, 160(%r28)
	std %r3, 168(%r28)
	li %r3, 0
	std %r3, 192(%r28)
	std %r5, 176(%r28)
	std %r6, 184(%r28)
2325:
2323:
	b 2321f
2320:
	li %r5, 0
	li %r6, 0
	ld %r3, 24(%r28)
	std %r3, 168(%r28)
	li %r3, 1
	std %r3, 192(%r28)
	std %r5, 176(%r28)
	std %r6, 184(%r28)
2321:
	ld %r3, 64(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2330f
	ld %r3, 0(%r28)
	li %r5, 544
	li %r0, 0
2332:
	stb %r0, 0(%r3)
	addi %r3, %r3, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2332b
	b 2331f
2330:
	addi %r3, %r28, 2208
	ld %r4, 0(%r28)
	li %r5, 544
2333:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2333b
2331:
	ld %r3, 152(%r28)
	ld %r4, 176(%r28)
	std %r4, 0(%r3)
	ld %r4, 184(%r28)
	std %r4, 24(%r3)
	ld %r3, 144(%r28)
	ld %r4, 168(%r28)
	std %r4, 0(%r3)
	ld %r3, 192(%r28)
23:
	b 21f
20:
	li %r0, 0
	std %r0, 512(%r28)
	std %r0, 520(%r28)
	std %r0, 528(%r28)
	std %r0, 536(%r28)
	std %r0, 544(%r28)
	std %r0, 552(%r28)
	std %r0, 560(%r28)
	std %r0, 568(%r28)
	li %r0, 128
	stb %r0, 532(%r28)
	li %r0, 0
	stb %r0, 574(%r28)
	li %r0, 160
	stb %r0, 575(%r28)
2334:
	ld %r3, 16(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2335f
	ld %r3, 80(%r28)
	ld %r4, 160(%r28)
	subf %r3, %r4, %r3
	li %r4, 20
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2337f
	ld %r3, 72(%r28)
	ld %r4, 160(%r28)
	add %r3, %r3, %r4
	std %r3, 8(%r28)
	addi %r4, %r4, 20
	std %r4, 24(%r28)
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 20
2339:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2339b
	lis %r0, 26437
	ori %r0, %r0, 8961
	stw %r0, 576(%r28)
	lis %r0, -4147
	ori %r0, %r0, 43913
	stw %r0, 580(%r28)
	lis %r0, -26438
	ori %r0, %r0, 56574
	stw %r0, 584(%r28)
	lis %r0, 4146
	ori %r0, %r0, 21622
	stw %r0, 588(%r28)
	lis %r0, -15406
	ori %r0, %r0, 57840
	stw %r0, 592(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 9600
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha1_compress}
	addi %r28, %r28, 608
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -608
	lbz %r0, 608(%r28)
	ori %r0, %r0, 128
	stb %r0, 608(%r28)
	lbz %r0, 627(%r28)
	ori %r0, %r0, 1
	stb %r0, 627(%r28)
	addi %r3, %r28, 608
	addi %r4, %r28, 9600
	li %r5, 20
2340:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2340b
	addi %r3, %r28, 9600
	li %r4, 8016
	ld %r9, 24(%r28)
	ld %r5, 72(%r28)
	ld %r6, 80(%r28)
	add %r5, %r5, %r9
	subf %r6, %r9, %r6
	addi %r7, %r28, 112
	cmpldi %cr0, %r6, 0
	beq %cr0, 2341f
	b 2342f
2341:
	ld %r5, 72(%r28)
2342:
	bl {vg_dsa_probable_prime_160}
	rlwinm %r3, %r3, 0, 0, 31
	std %r3, 88(%r28)
	cmpldi %cr0, %r3, 0
	beq %cr0, 2343f
	ld %r4, 112(%r28)
	ld %r5, 24(%r28)
	add %r5, %r5, %r4
	std %r5, 24(%r28)
	b 2344f
2343:
2344:
	ld %r3, 88(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2345f
	ld %r3, 88(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2347f
	b 2348f
2347:
	li %r3, 0
	std %r3, 32(%r28)
	li %r3, 1
	std %r3, 40(%r28)
	li %r3, 4
	std %r3, 96(%r28)
2349:
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 20
2350:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2350b
	addi %r3, %r28, 531
	ld %r4, 40(%r28)
	addi %r4, %r4, 0
	li %r6, 20
2351:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2351b
	lis %r0, 26437
	ori %r0, %r0, 8961
	stw %r0, 576(%r28)
	lis %r0, -4147
	ori %r0, %r0, 43913
	stw %r0, 580(%r28)
	lis %r0, -26438
	ori %r0, %r0, 56574
	stw %r0, 584(%r28)
	lis %r0, 4146
	ori %r0, %r0, 21622
	stw %r0, 588(%r28)
	lis %r0, -15406
	ori %r0, %r0, 57840
	stw %r0, 592(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 9600
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha1_compress}
	addi %r28, %r28, 780
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -780
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 20
2352:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2352b
	addi %r3, %r28, 531
	ld %r4, 40(%r28)
	addi %r4, %r4, 1
	li %r6, 20
2353:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2353b
	lis %r0, 26437
	ori %r0, %r0, 8961
	stw %r0, 576(%r28)
	lis %r0, -4147
	ori %r0, %r0, 43913
	stw %r0, 580(%r28)
	lis %r0, -26438
	ori %r0, %r0, 56574
	stw %r0, 584(%r28)
	lis %r0, 4146
	ori %r0, %r0, 21622
	stw %r0, 588(%r28)
	lis %r0, -15406
	ori %r0, %r0, 57840
	stw %r0, 592(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 9600
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha1_compress}
	addi %r28, %r28, 760
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -760
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 20
2354:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2354b
	addi %r3, %r28, 531
	ld %r4, 40(%r28)
	addi %r4, %r4, 2
	li %r6, 20
2355:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2355b
	lis %r0, 26437
	ori %r0, %r0, 8961
	stw %r0, 576(%r28)
	lis %r0, -4147
	ori %r0, %r0, 43913
	stw %r0, 580(%r28)
	lis %r0, -26438
	ori %r0, %r0, 56574
	stw %r0, 584(%r28)
	lis %r0, 4146
	ori %r0, %r0, 21622
	stw %r0, 588(%r28)
	lis %r0, -15406
	ori %r0, %r0, 57840
	stw %r0, 592(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 9600
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha1_compress}
	addi %r28, %r28, 740
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -740
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 20
2356:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2356b
	addi %r3, %r28, 531
	ld %r4, 40(%r28)
	addi %r4, %r4, 3
	li %r6, 20
2357:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2357b
	lis %r0, 26437
	ori %r0, %r0, 8961
	stw %r0, 576(%r28)
	lis %r0, -4147
	ori %r0, %r0, 43913
	stw %r0, 580(%r28)
	lis %r0, -26438
	ori %r0, %r0, 56574
	stw %r0, 584(%r28)
	lis %r0, 4146
	ori %r0, %r0, 21622
	stw %r0, 588(%r28)
	lis %r0, -15406
	ori %r0, %r0, 57840
	stw %r0, 592(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 9600
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha1_compress}
	addi %r28, %r28, 720
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -720
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 20
2358:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2358b
	addi %r3, %r28, 531
	ld %r4, 40(%r28)
	addi %r4, %r4, 4
	li %r6, 20
2359:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2359b
	lis %r0, 26437
	ori %r0, %r0, 8961
	stw %r0, 576(%r28)
	lis %r0, -4147
	ori %r0, %r0, 43913
	stw %r0, 580(%r28)
	lis %r0, -26438
	ori %r0, %r0, 56574
	stw %r0, 584(%r28)
	lis %r0, 4146
	ori %r0, %r0, 21622
	stw %r0, 588(%r28)
	lis %r0, -15406
	ori %r0, %r0, 57840
	stw %r0, 592(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 9600
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha1_compress}
	addi %r28, %r28, 700
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -700
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 20
2360:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2360b
	addi %r3, %r28, 531
	ld %r4, 40(%r28)
	addi %r4, %r4, 5
	li %r6, 20
2361:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2361b
	lis %r0, 26437
	ori %r0, %r0, 8961
	stw %r0, 576(%r28)
	lis %r0, -4147
	ori %r0, %r0, 43913
	stw %r0, 580(%r28)
	lis %r0, -26438
	ori %r0, %r0, 56574
	stw %r0, 584(%r28)
	lis %r0, 4146
	ori %r0, %r0, 21622
	stw %r0, 588(%r28)
	lis %r0, -15406
	ori %r0, %r0, 57840
	stw %r0, 592(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 9600
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha1_compress}
	addi %r28, %r28, 680
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -680
	ld %r3, 8(%r28)
	addi %r4, %r28, 512
	li %r5, 20
2362:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2362b
	addi %r3, %r28, 531
	ld %r4, 40(%r28)
	addi %r4, %r4, 6
	li %r6, 20
2363:
	lbz %r5, 0(%r3)
	add %r5, %r5, %r4
	stb %r5, 0(%r3)
	rldicl %r4, %r5, 56, 8
	addi %r3, %r3, -1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2363b
	lis %r0, 26437
	ori %r0, %r0, 8961
	stw %r0, 576(%r28)
	lis %r0, -4147
	ori %r0, %r0, 43913
	stw %r0, 580(%r28)
	lis %r0, -26438
	ori %r0, %r0, 56574
	stw %r0, 584(%r28)
	lis %r0, 4146
	ori %r0, %r0, 21622
	stw %r0, 588(%r28)
	lis %r0, -15406
	ori %r0, %r0, 57840
	stw %r0, 592(%r28)
	addi %r26, %r28, 576
	addi %r27, %r28, 9600
	addi %r4, %r28, 512
	addi %r3, %r26, 0
	li %r5, 1
	addi %r6, %r27, 0
	bl {vg_sha1_compress}
	addi %r28, %r28, 660
	lwz %r8, 0(%r26)
	li %r11, 0
	stwbrx %r8, %r28, %r11
	lwz %r8, 4(%r26)
	li %r11, 4
	stwbrx %r8, %r28, %r11
	lwz %r8, 8(%r26)
	li %r11, 8
	stwbrx %r8, %r28, %r11
	lwz %r8, 12(%r26)
	li %r11, 12
	stwbrx %r8, %r28, %r11
	lwz %r8, 16(%r26)
	li %r11, 16
	stwbrx %r8, %r28, %r11
	addi %r28, %r28, -660
	lbz %r0, 672(%r28)
	ori %r0, %r0, 128
	stb %r0, 672(%r28)
	addi %r31, %r28, 7360
	li %r29, 32
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r8, 15
	mulld %r8, %r8, %r30
	rldicl %r8, %r8, 62, 2
	addi %r5, %r31, 160
	li %r0, 0
2364:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2364b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	addi %r6, %r28, 672
	li %r8, 128
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
2365:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2365b
	addi %r6, %r28, 672
	li %r8, 128
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
2366:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2366b
	addi %r6, %r28, 608
	li %r8, 20
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
2367:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2367b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2368:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2368b
	rldicr %r4, %r29, 5, 58
2369:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2370f
	addi %r8, %r29, 0
2372:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2372b
	b 2371f
2370:
	rldicl %r8, %r29, 63, 1
2373:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2373b
2371:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2374f
	addi %r8, %r29, 1
2376:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2376b
	b 2375f
2374:
	rldicl %r8, %r29, 63, 1
2377:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2377b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2375:
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2378f
	addi %r8, %r29, 1
	li %r9, 0
2380:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2380b
	b 2379f
2378:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2381:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2381b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2379:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 3
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2382f
	addi %r8, %r29, 1
2384:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2384b
	b 2383f
2382:
	rldicl %r8, %r29, 63, 1
2385:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2385b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2383:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2369b
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2386f
	addi %r8, %r29, 0
	li %r9, 0
2388:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2388b
	b 2387f
2386:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2389:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2389b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2387:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 136(%r31)
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 136(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2390f
	addi %r8, %r29, 0
2392:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2392b
	b 2391f
2390:
	rldicl %r8, %r29, 63, 1
2393:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2393b
2391:
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2394f
	addi %r8, %r29, 0
	li %r9, 0
2396:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2396b
	b 2395f
2394:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2397:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2397b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2395:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2398f
	addi %r8, %r29, 0
2400:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2400b
	b 2399f
2398:
	rldicl %r8, %r29, 63, 1
2401:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2401b
2399:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2402f
	addi %r8, %r29, 0
2404:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2404b
	b 2403f
2402:
	rldicl %r8, %r29, 63, 1
2405:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2405b
2403:
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	addi %r5, %r28, 1056
	li %r8, 128
	li %r9, 0
	addi %r9, %r9, -1
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2406:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2406b
	addi %r5, %r28, 1440
	li %r8, 109
	li %r9, 0
	addi %r9, %r9, -1
	li %r6, 9
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2407:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2407b
	lbz %r0, 1056(%r28)
	rldicl %r0, %r0, 57, 7
	cmpldi %cr0, %r0, 0
	beq %cr0, 2408f
	addi %r3, %r28, 1056
	addi %r4, %r28, 9600
	li %r5, 128
2410:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2410b
	addi %r3, %r28, 9600
	li %r4, 8016
	ld %r9, 24(%r28)
	ld %r5, 72(%r28)
	ld %r6, 80(%r28)
	add %r5, %r5, %r9
	subf %r6, %r9, %r6
	addi %r7, %r28, 112
	cmpldi %cr0, %r6, 0
	beq %cr0, 2411f
	b 2412f
2411:
	ld %r5, 72(%r28)
2412:
	bl {vg_dsa_probable_prime_1024}
	rlwinm %r3, %r3, 0, 0, 31
	std %r3, 88(%r28)
	cmpldi %cr0, %r3, 0
	beq %cr0, 2413f
	ld %r4, 112(%r28)
	ld %r5, 24(%r28)
	add %r5, %r5, %r4
	std %r5, 24(%r28)
	b 2414f
2413:
2414:
	ld %r3, 88(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2415f
	ld %r3, 88(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2417f
	b 2418f
2417:
	li %r3, 1
	std %r3, 96(%r28)
2418:
	b 2416f
2415:
	li %r3, 0
	std %r3, 96(%r28)
2416:
	b 2409f
2408:
2409:
	ld %r3, 96(%r28)
	addi %r0, %r3, -4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2419f
	b 2420f
2419:
	ld %r3, 32(%r28)
	addi %r3, %r3, 1
	std %r3, 32(%r28)
	ld %r4, 40(%r28)
	addi %r4, %r4, 7
	std %r4, 40(%r28)
	addi %r0, %r3, -4096
	cmpldi %cr0, %r0, 0
	beq %cr0, 2421f
	b 2422f
2421:
	li %r3, 2
	std %r3, 96(%r28)
2422:
2420:
	ld %r3, 96(%r28)
	addi %r0, %r3, -4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2349b
	ld %r3, 96(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2423f
	ld %r3, 96(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2425f
	b 2426f
2425:
	ld %r3, 72(%r28)
	ld %r4, 24(%r28)
	add %r3, %r3, %r4
	std %r3, 128(%r28)
	ld %r3, 80(%r28)
	subf %r3, %r4, %r3
	li %r4, 128
	rldicr %r4, %r4, 7, 56
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2427f
	std %r4, 136(%r28)
	b 2428f
2427:
	std %r3, 136(%r28)
2428:
	ld %r3, 128(%r28)
	std %r3, 48(%r28)
	ld %r3, 136(%r28)
	std %r3, 56(%r28)
	li %r3, 4
	std %r3, 104(%r28)
2429:
	ld %r3, 56(%r28)
	li %r4, 128
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2430f
	addi %r31, %r28, 7360
	li %r29, 32
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2432f
	addi %r8, %r29, 0
2434:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2434b
	b 2433f
2432:
	rldicl %r8, %r29, 63, 1
2435:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2435b
2433:
	ld %r6, 48(%r28)
	li %r8, 128
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
2436:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2436b
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 10
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2437f
	addi %r8, %r29, 0
	li %r9, 0
2439:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2439b
	b 2438f
2437:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2440:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2440b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2438:
	stw %r9, 140(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2441f
	addi %r8, %r29, 0
	li %r9, 0
2443:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subf %r0, %r3, %r0
	subf %r0, %r9, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2443b
	b 2442f
2441:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2444:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2444b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2442:
	stw %r9, 144(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 144(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	lwz %r0, 140(%r31)
	cmpldi %cr0, %r0, 0
	beq %cr0, 2445f
	addi %r21, %r28, 3072
	addi %r23, %r21, 0
	addi %r31, %r21, 0
	addi %r10, %r21, 256
	li %r11, 32
	li %r29, 144
	addi %r12, %r28, 1056
	li %r6, 128
	addi %r10, %r10, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2447:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2447b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2448:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2448b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2449:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2449b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 6, 57
2450:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
2451:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2451b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2452:
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
	bne %cr0, 2452b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
2453:
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
	bne %cr0, 2453b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2450b
	ld %r12, 48(%r28)
	li %r6, 128
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2454:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2454b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2455:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2455b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
	addi %r30, %r28, 1440
	li %r31, 109
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
2456:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2456b
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
	bl {vg_rsa_mont_kernel}
	mtlr %r14
2457:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
	li %r25, 8
2458:
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
	addi %r7, %r10, 0
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
	mflr %r14
	addi %r3, %r12, 0
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r6, %r10, 0
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
	rldicl %r0, %r24, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	rldicr %r24, %r24, 1, 62
	addi %r8, %r10, 0
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
	addi %r17, %r11, 0
2459:
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
	bne %cr0, 2459b
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 2458b
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2457b
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
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
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
2460:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2460b
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
	addi %r10, %r31, 256
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2461:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2461b
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2462:
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
	bne %cr0, 2462b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
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
2463:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2463b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
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
2464:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2464b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	addi %r3, %r20, 0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2465f
	b 2466f
2465:
	addi %r12, %r28, 1824
	li %r6, 128
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2467:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2467b
	li %r3, 1
	std %r3, 104(%r28)
2466:
	b 2446f
2445:
2446:
	ld %r3, 48(%r28)
	addi %r3, %r3, 128
	std %r3, 48(%r28)
	ld %r3, 56(%r28)
	addi %r3, %r3, -128
	std %r3, 56(%r28)
	b 2431f
2430:
	li %r3, 2
	std %r3, 104(%r28)
2431:
	ld %r3, 104(%r28)
	addi %r0, %r3, -4
	cmpldi %cr0, %r0, 0
	beq %cr0, 2429b
	ld %r3, 48(%r28)
	ld %r4, 72(%r28)
	subf %r3, %r4, %r3
	std %r3, 24(%r28)
	ld %r3, 104(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2468f
	ld %r3, 136(%r28)
	li %r4, 128
	rldicr %r4, %r4, 7, 56
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2470f
	b 2471f
2470:
	li %r3, 2
	std %r3, 64(%r28)
2471:
	b 2469f
2468:
	addi %r3, %r28, 1056
	addi %r4, %r28, 2208
	li %r5, 128
2472:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2472b
	addi %r3, %r28, 608
	addi %r4, %r28, 2336
	li %r5, 20
2473:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2473b
	addi %r3, %r28, 1824
	addi %r4, %r28, 2356
	li %r5, 128
2474:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2474b
	addi %r3, %r28, 2208
	li %r4, 276
	li %r5, 128
	li %r6, 20
	addi %r7, %r28, 9600
	li %r8, 8016
	bl {vg_dsa_check_parameters}
	rlwinm %r3, %r3, 0, 0, 31
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2475f
	b 2476f
2475:
	li %r3, 1
	std %r3, 64(%r28)
2476:
2469:
2426:
	b 2424f
2423:
	li %r3, 2
	std %r3, 64(%r28)
2424:
2348:
	b 2346f
2345:
	li %r3, 2
	std %r3, 64(%r28)
2346:
	ld %r3, 64(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2477f
	b 2478f
2477:
	ld %r3, 24(%r28)
	std %r3, 160(%r28)
	ld %r3, 16(%r28)
	addi %r3, %r3, -1
	std %r3, 16(%r28)
2478:
	b 2338f
2337:
	li %r3, 2
	std %r3, 64(%r28)
2338:
	b 2336f
2335:
	li %r3, 3
	std %r3, 64(%r28)
2336:
	ld %r3, 64(%r28)
	addi %r0, %r3, -0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2334b
	ld %r3, 64(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2479f
	ld %r3, 64(%r28)
	addi %r0, %r3, -2
	cmpldi %cr0, %r0, 0
	beq %cr0, 2481f
	li %r5, 0
	li %r6, 0
	ld %r3, 160(%r28)
	std %r3, 168(%r28)
	li %r3, 3
	std %r3, 192(%r28)
	std %r5, 176(%r28)
	std %r6, 184(%r28)
	b 2482f
2481:
	ld %r3, 80(%r28)
	ld %r4, 160(%r28)
	subf %r3, %r4, %r3
	li %r4, 128
	rldicr %r5, %r4, 15, 48
	add %r4, %r4, %r5
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2483f
	li %r5, 0
	li %r6, 0
	ld %r3, 160(%r28)
	std %r3, 168(%r28)
	li %r3, 3
	std %r3, 192(%r28)
	std %r5, 176(%r28)
	std %r6, 184(%r28)
	b 2484f
2483:
	li %r4, 128
	rldicr %r4, %r4, 8, 55
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2485f
	b 2486f
2485:
	addi %r3, %r4, 0
2486:
	add %r3, %r3, %r3
	li %r4, 128
	rldicr %r5, %r4, 15, 48
	add %r4, %r4, %r5
	subfc %r0, %r4, %r3
	li %r0, 0
	addze %r0, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2487f
	addi %r3, %r4, 0
	b 2488f
2487:
2488:
	addi %r6, %r3, 0
	ld %r5, 16(%r28)
	ld %r3, 160(%r28)
	std %r3, 168(%r28)
	li %r3, 0
	std %r3, 192(%r28)
	std %r5, 176(%r28)
	std %r6, 184(%r28)
2484:
2482:
	b 2480f
2479:
	li %r5, 0
	li %r6, 0
	ld %r3, 24(%r28)
	std %r3, 168(%r28)
	li %r3, 1
	std %r3, 192(%r28)
	std %r5, 176(%r28)
	std %r6, 184(%r28)
2480:
	ld %r3, 64(%r28)
	addi %r0, %r3, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2489f
	ld %r3, 0(%r28)
	li %r5, 276
	li %r0, 0
2491:
	stb %r0, 0(%r3)
	addi %r3, %r3, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2491b
	b 2490f
2489:
	addi %r3, %r28, 2208
	ld %r4, 0(%r28)
	li %r5, 276
2492:
	lbz %r6, 0(%r3)
	stb %r6, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2492b
2490:
	ld %r3, 152(%r28)
	ld %r4, 176(%r28)
	std %r4, 0(%r3)
	ld %r4, 184(%r28)
	std %r4, 24(%r3)
	ld %r3, 144(%r28)
	ld %r4, 168(%r28)
	std %r4, 0(%r3)
	ld %r3, 192(%r28)
21:
	ld %r0, 120(%r28)
	mtlr %r0
	ld %r2, 200(%r28)
	ld %r14, 208(%r28)
	ld %r15, 216(%r28)
	ld %r16, 224(%r28)
	ld %r17, 232(%r28)
	ld %r18, 240(%r28)
	ld %r19, 248(%r28)
	ld %r20, 256(%r28)
	ld %r21, 264(%r28)
	ld %r22, 272(%r28)
	ld %r23, 280(%r28)
	ld %r24, 288(%r28)
	ld %r25, 296(%r28)
	ld %r26, 304(%r28)
	ld %r27, 312(%r28)
	ld %r29, 320(%r28)
	ld %r30, 328(%r28)
	ld %r31, 336(%r28)
	ld %r28, 344(%r28)
	blr
