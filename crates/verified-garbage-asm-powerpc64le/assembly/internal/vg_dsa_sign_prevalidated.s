// The functions of `src/internal/vg_dsa_sign_prevalidated.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_sign_prevalidated:
	addi %r11, %r1, 104
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
	addi %r27, %r5, 0
	addi %r28, %r8, 0
	addi %r26, %r10, 0
	std %r3, 8(%r21)
	addi %r10, %r1, 96
	ld %r10, 0(%r10)
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
	rldicr %r0, %r9, 16, 47
	add %r2, %r7, %r0
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
	ld %r16, 8(%r21)
	rldicr %r17, %r2, 32, 31
	rldicl %r17, %r17, 16, 48
	add %r17, %r17, %r17
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
	ld %r16, 8(%r21)
	rldicr %r17, %r2, 32, 31
	rldicl %r17, %r17, 16, 48
	add %r17, %r17, %r17
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
	ld %r16, 8(%r21)
	rldicr %r17, %r2, 32, 31
	rldicl %r17, %r17, 16, 48
	add %r17, %r17, %r17
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
225:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 225b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
226:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 226b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	mflr %r25
	bl {vg_dsa_setup_p}
	mtlr %r25
	li %r3, 0
	addi %r3, %r3, -1
	std %r3, 0(%r21)
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
227:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 227b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
228:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 228b
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
229:
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
	bne %cr0, 229b
	addi %r30, %r24, 0
	rldicr %r31, %r2, 32, 31
	rldicl %r31, %r31, 16, 48
	mflr %r25
	bl {vg_bignum_pow_win}
	mtlr %r25
	addi %r31, %r23, 0
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
230:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 230b
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
231:
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
	bne %cr0, 231b
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
232:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 232b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 5, 58
	rldicl %r3, %r11, 63, 1
	add %r4, %r4, %r3
233:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
234:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 234b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
235:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 235b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
236:
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
	bne %cr0, 236b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 233b
	li %r24, 6
237:
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
238:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 238b
	rldicr %r9, %r11, 2, 61
	add %r16, %r10, %r9
	add %r15, %r7, %r9
	rldicr %r17, %r4, 32, 31
239:
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
	beq %cr0, 240f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 242f
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	beq %cr0, 244f
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
	b 245f
244:
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
245:
	b 243f
242:
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
243:
	b 241f
240:
241:
	cmplwi %cr0, %r17, 0
	beq %cr0, 246f
248:
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
	bne %cr0, 248b
	b 247f
246:
247:
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
	bne %cr0, 239b
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
249:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 249b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
250:
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
	bne %cr0, 250b
	addi %r24, %r24, -1
	cmpldi %cr0, %r24, 0
	bne %cr0, 237b
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
251:
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
	bne %cr0, 251b
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
252:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 252b
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
253:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 253b
254:
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r30, 0
	rldicl %r17, %r11, 63, 1
255:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 255b
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
256:
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
	bne %cr0, 256b
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
257:
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
	bne %cr0, 257b
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
258:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 258b
	rldicl %r3, %r11, 63, 1
	subf %r31, %r3, %r31
	addi %r3, %r31, -1
	rldicl %r3, %r3, 1, 63
	li %r0, 1
	xor %r3, %r3, %r0
	cmpldi %cr0, %r3, 0
	bne %cr0, 254b
	addi %r31, %r23, 0
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
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
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
260:
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
	bne %cr0, 260b
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
261:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 261b
	addi %r12, %r28, 0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
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
262:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 262b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
263:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 263b
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
	add %r12, %r12, %r6
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
264:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 264b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
265:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 265b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	ld %r22, 0(%r21)
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
266:
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
	bne %cr0, 266b
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
267:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 267b
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
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
268:
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
	bne %cr0, 268b
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
269:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 269b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	and %r22, %r22, %r20
	li %r20, 0
	addi %r20, %r20, -1
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
270:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 270b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	and %r22, %r22, %r20
	std %r22, 0(%r21)
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
271:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 271b
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
273:
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
	bne %cr0, 273b
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
274:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 274b
	addi %r12, %r28, 0
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
275:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 275b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
276:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 276b
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
277:
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
	bne %cr0, 277b
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
278:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 278b
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
279:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
	li %r25, 8
280:
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
281:
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
	bne %cr0, 281b
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 280b
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 279b
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
	beq %cr0, 282f
	b 283f
282:
	or %r6, %r0, %r0
283:
	addi %r12, %r26, 0
	cmpldi %cr0, %r6, 0
	beq %cr0, 284f
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
286:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 286b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
287:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 287b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r31, 256
	b 285f
284:
	addi %r14, %r10, 0
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
285:
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
289:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 289b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
290:
	lwz %r0, 0(%r15)
	lwz %r3, 0(%r16)
	add %r0, %r0, %r3
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 290b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
291:
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
	bne %cr0, 291b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
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
	addi %r17, %r11, 0
292:
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
	bne %cr0, 292b
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
	addi %r30, %r12, 0
	addi %r31, %r6, 0
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
293:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 293b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
294:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
	li %r25, 8
295:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	rldicl %r20, %r24, 1, 63
	rldicr %r24, %r24, 1, 62
296:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 296b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
297:
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
	bne %cr0, 297b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
298:
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
	bne %cr0, 298b
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 295b
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 294b
	addi %r31, %r23, 0
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
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
299:
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
	bne %cr0, 299b
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
2100:
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
	bne %cr0, 2100b
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
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r16, %r10, 0
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	add %r16, %r16, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
2101:
	lwz %r0, 0(%r15)
	lwz %r3, 0(%r16)
	add %r0, %r0, %r3
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r16, %r16, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2101b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2102:
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
	bne %cr0, 2102b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
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
	addi %r17, %r11, 0
2103:
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
	bne %cr0, 2103b
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
2104:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2104b
	ld %r22, 0(%r21)
	li %r20, 0
	addi %r20, %r20, -1
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
2105:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2105b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r19, %r3, %r0
	or %r20, %r20, %r19
	xor %r20, %r20, %r19
	and %r22, %r22, %r20
	addi %r20, %r22, 0
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
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2106:
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
	bne %cr0, 2106b
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
	add %r9, %r9, %r29
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2107:
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
	bne %cr0, 2107b
	ld %r12, 8(%r21)
	rldicr %r6, %r2, 32, 31
	rldicl %r6, %r6, 16, 48
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2108:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2108b
	add %r12, %r12, %r6
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2109:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2109b
	li %r0, 1
	and %r3, %r22, %r0
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
