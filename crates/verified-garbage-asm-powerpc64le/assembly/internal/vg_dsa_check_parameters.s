// The functions of `src/internal/vg_dsa_check_parameters.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_dsa_check_parameters:
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
248:
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
	beq %cr0, 249f
251:
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
	bne %cr0, 251b
	b 250f
249:
250:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 252f
254:
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
	bne %cr0, 254b
	b 253f
252:
253:
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
	bne %cr0, 248b
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
255:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 255b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
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
257:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 257b
258:
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
	beq %cr0, 259f
261:
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
	bne %cr0, 261b
	b 260f
259:
260:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 262f
264:
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
	bne %cr0, 264b
	b 263f
262:
263:
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
	bne %cr0, 258b
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
265:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 265b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
266:
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
	bne %cr0, 266b
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
267:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 267b
268:
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
	beq %cr0, 269f
271:
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
	bne %cr0, 271b
	b 270f
269:
270:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 272f
274:
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
	bne %cr0, 274b
	b 273f
272:
273:
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
	bne %cr0, 268b
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
275:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 275b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
276:
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
	bne %cr0, 276b
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
287:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 287b
288:
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
	beq %cr0, 289f
291:
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
	bne %cr0, 291b
	b 290f
289:
290:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 292f
294:
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
	bne %cr0, 294b
	b 293f
292:
293:
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
	bne %cr0, 288b
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
295:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 295b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
296:
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
	bne %cr0, 296b
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
297:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 297b
298:
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
	beq %cr0, 299f
2101:
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
	bne %cr0, 2101b
	b 2100f
299:
2100:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2102f
2104:
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
	bne %cr0, 2104b
	b 2103f
2102:
2103:
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
	bne %cr0, 298b
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2105:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2105b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
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
	b 241f
240:
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2108:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2108b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 5, 58
	rldicl %r3, %r11, 63, 1
	add %r4, %r4, %r3
2109:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
2110:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2110b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2111:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2111b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2112:
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
	bne %cr0, 2112b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2109b
	li %r24, 6
2113:
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
2114:
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2114b
2115:
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
	beq %cr0, 2116f
2118:
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
	bne %cr0, 2118b
	b 2117f
2116:
2117:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2119f
2121:
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
	bne %cr0, 2121b
	b 2120f
2119:
2120:
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
	bne %cr0, 2115b
	rldicr %r12, %r22, 32, 31
	rldicl %r12, %r12, 32, 32
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2122:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2122b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2123:
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
	bne %cr0, 2123b
	addi %r24, %r24, -1
	cmpldi %cr0, %r24, 0
	bne %cr0, 2113b
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
2125:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2125b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2126:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2126b
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
2127:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2127b
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
2128:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2128b
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
2129:
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
	bne %cr0, 2129b
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
2130:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2130b
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
2131:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2131b
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
	beq %cr0, 2132f
	b 2133f
2132:
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
2134:
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
	bne %cr0, 2134b
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
2135:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2135b
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
	li %r24, 2
2137:
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
2138:
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
	bne %cr0, 2138b
	addi %r24, %r24, 1
	addi %r4, %r24, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2137b
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
2140:
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
	li %r19, 0
2141:
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r0, 0
	subf %r20, %r3, %r0
	addi %r8, %r19, 8
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
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
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2142:
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
	bne %cr0, 2142b
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r0, 0
	subf %r20, %r3, %r0
	addi %r8, %r19, 8
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r9, %r10, 0
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
2143:
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
	bne %cr0, 2143b
	addi %r19, %r19, 1
	addi %r4, %r19, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2141b
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
	li %r19, 0
2144:
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r0, 0
	subf %r20, %r3, %r0
	addi %r8, %r19, 8
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
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
	addi %r19, %r19, 1
	xor %r3, %r19, %r18
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r0, 0
	subf %r20, %r3, %r0
	addi %r8, %r19, 8
	mulld %r8, %r8, %r29
	add %r8, %r8, %r10
	addi %r9, %r10, 0
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
2146:
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
	bne %cr0, 2146b
	addi %r19, %r19, 1
	addi %r4, %r19, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2144b
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
	bne %cr0, 2140b
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
2147:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2147b
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
2148:
	ld %r0, 0(%r14)
	ld %r4, 0(%r15)
	xor %r0, %r0, %r4
	or %r3, %r3, %r0
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2148b
	li %r0, 0
	subfc %r3, %r3, %r0
	addze %r3, %r0
	subf %r3, %r3, %r0
	li %r4, 1
	and %r3, %r3, %r4
	xor %r0, %r3, %r4
2133:
	cmpldi %cr0, %r0, 0
	beq %cr0, 2149f
	li %r3, 0
	b 2150f
2149:
	li %r3, 1
2150:
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
