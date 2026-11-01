// The functions of `src/rsa_keygen.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_keygen_key:
	addi %r11, %r1, 160
	ld %r11, 0(%r11)
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
	std %r29, 88(%r11)
	std %r30, 96(%r11)
	std %r31, 104(%r11)
	addi %r31, %r11, 0
	addi %r14, %r3, 0
	addi %r15, %r5, 0
	addi %r16, %r7, 0
	addi %r17, %r9, 0
	addi %r22, %r8, 0
	addi %r24, %r4, 0
	addi %r18, %r1, 96
	ld %r18, 0(%r18)
	addi %r19, %r1, 112
	ld %r19, 0(%r19)
	addi %r20, %r1, 128
	ld %r20, 0(%r20)
	addi %r21, %r1, 144
	ld %r21, 0(%r21)
	addi %r23, %r1, 152
	ld %r23, 0(%r23)
	rldicl %r29, %r22, 63, 1
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r8, 60
	mulld %r8, %r8, %r30
	rldicl %r8, %r8, 62, 2
	addi %r5, %r31, 160
	li %r0, 0
20:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	addi %r6, %r16, 0
	addi %r8, %r22, 0
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
21:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21b
	addi %r6, %r17, 0
	addi %r8, %r22, 0
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
22:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 22b
	addi %r6, %r21, 0
	addi %r8, %r23, 0
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
23:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 23b
	li %r6, 0
	li %r5, 15
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r6
	li %r0, 1
	stw %r0, 0(%r5)
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r6
	li %r0, 2
	stw %r0, 0(%r5)
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r6
	li %r0, 3
	stw %r0, 0(%r5)
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r6
	li %r0, 1
	stw %r0, 0(%r5)
	addi %r6, %r22, 0
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r6
	li %r0, 1
	stw %r0, 0(%r5)
	li %r6, 4
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r6
	li %r0, 2
	stw %r0, 0(%r5)
	li %r9, 1
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	addi %r8, %r29, 0
26:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 26b
	b 25f
24:
	rldicl %r8, %r29, 63, 1
27:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 27b
25:
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 23
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 28f
	addi %r8, %r29, 0
	li %r9, 0
210:
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
	bne %cr0, 210b
	b 29f
28:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
211:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 211b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
29:
	stw %r9, 112(%r31)
	li %r5, 24
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 23
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 112(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 212f
	addi %r8, %r29, 0
214:
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
	bne %cr0, 214b
	b 213f
212:
	rldicl %r8, %r29, 63, 1
215:
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
	bne %cr0, 215b
213:
	li %r5, 25
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 23
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 22
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 112(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 216f
	addi %r8, %r29, 0
218:
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
	bne %cr0, 218b
	b 217f
216:
	rldicl %r8, %r29, 63, 1
219:
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
	bne %cr0, 219b
217:
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 24
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 220f
	addi %r8, %r29, 0
	li %r9, 0
222:
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
	bne %cr0, 222b
	b 221f
220:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
223:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 223b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
221:
	stw %r9, 112(%r31)
	li %r5, 26
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 28
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 10
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 112(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 224f
	addi %r8, %r29, 0
226:
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
	bne %cr0, 226b
	b 225f
224:
	rldicl %r8, %r29, 63, 1
227:
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
	bne %cr0, 227b
225:
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 25
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 228f
	addi %r8, %r29, 0
	li %r9, 0
230:
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
	bne %cr0, 230b
	b 229f
228:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
231:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 231b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
229:
	stw %r9, 112(%r31)
	li %r5, 27
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 28
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 10
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 112(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 232f
	addi %r8, %r29, 0
234:
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
	bne %cr0, 234b
	b 233f
232:
	rldicl %r8, %r29, 63, 1
235:
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
	bne %cr0, 235b
233:
	li %r5, 56
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 26
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 236f
	addi %r8, %r29, 0
238:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 238b
	b 237f
236:
	rldicl %r8, %r29, 63, 1
239:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 239b
237:
	li %r5, 57
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 27
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 240f
	addi %r8, %r29, 0
242:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 242b
	b 241f
240:
	rldicl %r8, %r29, 63, 1
243:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 243b
241:
	li %r5, 55
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 244f
	addi %r8, %r29, 0
246:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 246b
	b 245f
244:
	rldicl %r8, %r29, 63, 1
247:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 247b
245:
	rldicr %r11, %r22, 3, 60
248:
	li %r5, 57
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 124(%r31)
	li %r5, 58
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 56
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 249f
	addi %r8, %r29, 0
251:
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
	bne %cr0, 251b
	b 250f
249:
	rldicl %r8, %r29, 63, 1
252:
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
	bne %cr0, 252b
250:
	li %r5, 59
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 58
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 253f
	addi %r8, %r29, 0
	li %r9, 0
255:
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
	bne %cr0, 255b
	b 254f
253:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
256:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 256b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
254:
	li %r5, 55
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 55
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 59
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 257f
	addi %r8, %r29, 0
	li %r9, 0
259:
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
	bne %cr0, 259b
	b 258f
257:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
260:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 260b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
258:
	li %r5, 59
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 56
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 261f
	addi %r8, %r29, 0
	li %r9, 0
263:
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
	bne %cr0, 263b
	b 262f
261:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
264:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 264b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
262:
	li %r5, 56
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 56
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 59
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 265f
	addi %r8, %r29, 0
	li %r9, 0
267:
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
	bne %cr0, 267b
	b 266f
265:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
268:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 268b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
266:
	li %r9, 0
	li %r5, 57
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 269f
	addi %r8, %r29, 0
271:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 271b
	b 270f
269:
	rldicl %r8, %r29, 63, 1
272:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 272b
270:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 248b
	li %r5, 32
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 55
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 273f
	addi %r8, %r29, 0
275:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 275b
	b 274f
273:
	rldicl %r8, %r29, 63, 1
276:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 276b
274:
	li %r5, 30
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 26
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 277f
	addi %r8, %r29, 0
279:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 279b
	b 278f
277:
	rldicl %r8, %r29, 63, 1
280:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 280b
278:
	li %r5, 31
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 27
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 281f
	addi %r8, %r29, 0
283:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 283b
	b 282f
281:
	rldicl %r8, %r29, 63, 1
284:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 284b
282:
	rldicr %r11, %r22, 3, 60
285:
	li %r5, 30
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 112(%r31)
	li %r5, 31
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 116(%r31)
	lwz %r0, 116(%r31)
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 116(%r31)
	lwz %r0, 112(%r31)
	li %r3, 1
	xor %r0, %r0, %r3
	lwz %r3, 116(%r31)
	and %r0, %r0, %r3
	stw %r0, 120(%r31)
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 30
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 286f
	addi %r8, %r29, 0
288:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 288b
	b 287f
286:
	rldicl %r8, %r29, 63, 1
289:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 289b
287:
	li %r9, 0
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 290f
	addi %r8, %r29, 0
292:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 292b
	b 291f
290:
	rldicl %r8, %r29, 63, 1
293:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 293b
291:
	li %r5, 30
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 30
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 28
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 120(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 294f
	addi %r8, %r29, 0
296:
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
	bne %cr0, 296b
	b 295f
294:
	rldicl %r8, %r29, 63, 1
297:
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
	bne %cr0, 297b
295:
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 31
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 298f
	addi %r8, %r29, 0
2100:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2100b
	b 299f
298:
	rldicl %r8, %r29, 63, 1
2101:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2101b
299:
	li %r9, 0
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2102f
	addi %r8, %r29, 0
2104:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2104b
	b 2103f
2102:
	rldicl %r8, %r29, 63, 1
2105:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2105b
2103:
	li %r5, 31
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 31
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 28
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 120(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2106f
	addi %r8, %r29, 0
2108:
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
	bne %cr0, 2108b
	b 2107f
2106:
	rldicl %r8, %r29, 63, 1
2109:
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
	bne %cr0, 2109b
2107:
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 32
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2110f
	addi %r8, %r29, 0
2112:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2112b
	b 2111f
2110:
	rldicl %r8, %r29, 63, 1
2113:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2113b
2111:
	li %r9, 0
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2114f
	addi %r8, %r29, 0
2116:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2116b
	b 2115f
2114:
	rldicl %r8, %r29, 63, 1
2117:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2117b
2115:
	li %r5, 32
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 32
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 28
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 120(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2118f
	addi %r8, %r29, 0
2120:
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
	bne %cr0, 2120b
	b 2119f
2118:
	rldicl %r8, %r29, 63, 1
2121:
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
	bne %cr0, 2121b
2119:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 285b
	li %r5, 31
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 112(%r31)
	lwz %r0, 112(%r31)
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 112(%r31)
	li %r5, 33
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 30
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 31
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 112(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2122f
	addi %r8, %r29, 0
2124:
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
	bne %cr0, 2124b
	b 2123f
2122:
	rldicl %r8, %r29, 63, 1
2125:
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
	bne %cr0, 2125b
2123:
	li %r5, 34
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 31
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 30
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 112(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2126f
	addi %r8, %r29, 0
2128:
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
	bne %cr0, 2128b
	b 2127f
2126:
	rldicl %r8, %r29, 63, 1
2129:
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
	bne %cr0, 2129b
2127:
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 34
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 16
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2130f
	addi %r8, %r29, 0
	li %r9, 0
2132:
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
	bne %cr0, 2132b
	b 2131f
2130:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2133:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2133b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2131:
	stw %r9, 116(%r31)
	li %r5, 29
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 34
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 116(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2134f
	addi %r8, %r29, 0
2136:
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
	bne %cr0, 2136b
	b 2135f
2134:
	rldicl %r8, %r29, 63, 1
2137:
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
	bne %cr0, 2137b
2135:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 29
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2138f
	addi %r8, %r29, 0
2140:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2140b
	b 2139f
2138:
	rldicl %r8, %r29, 63, 1
2141:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2141b
2139:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 33
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2142f
	addi %r8, %r29, 0
2144:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2144b
	b 2143f
2142:
	rldicl %r8, %r29, 63, 1
2145:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2145b
2143:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2146f
	addi %r8, %r29, 0
2148:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2148b
	b 2147f
2146:
	rldicl %r8, %r29, 63, 1
2149:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2149b
2147:
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2150f
	addi %r8, %r29, 0
2152:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2152b
	b 2151f
2150:
	rldicl %r8, %r29, 63, 1
2153:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2153b
2151:
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2154f
	addi %r8, %r29, 0
2156:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2156b
	b 2155f
2154:
	rldicl %r8, %r29, 63, 1
2157:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2157b
2155:
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 8
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2158f
	addi %r8, %r29, 0
	li %r9, 0
2160:
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
	bne %cr0, 2160b
	b 2159f
2158:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2161:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2161b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2159:
	rldicr %r4, %r29, 5, 58
2162:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 124(%r31)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 2163f
	addi %r8, %r29, 0
	li %r9, 0
2165:
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
	bne %cr0, 2165b
	b 2164f
2163:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2166:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2166b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2164:
	stw %r9, 128(%r31)
	lwz %r0, 124(%r31)
	lwz %r3, 128(%r31)
	and %r0, %r0, %r3
	stw %r0, 132(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 0
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2167f
	addi %r8, %r29, 0
	li %r9, 0
2169:
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
	bne %cr0, 2169b
	b 2168f
2167:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2170:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2170b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2168:
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 0
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2171f
	addi %r8, %r29, 0
2173:
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
	bne %cr0, 2173b
	b 2172f
2171:
	rldicl %r8, %r29, 63, 1
2174:
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
	bne %cr0, 2174b
2172:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2175f
	addi %r8, %r29, 0
2177:
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
	bne %cr0, 2177b
	b 2176f
2175:
	rldicl %r8, %r29, 63, 1
2178:
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
	bne %cr0, 2178b
2176:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2179f
	addi %r8, %r29, 0
2181:
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
	bne %cr0, 2181b
	b 2180f
2179:
	rldicl %r8, %r29, 63, 1
2182:
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
	bne %cr0, 2182b
2180:
	li %r9, 0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2183f
	addi %r8, %r29, 0
2185:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2185b
	b 2184f
2183:
	rldicl %r8, %r29, 63, 1
2186:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2186b
2184:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
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
	beq %cr0, 2187f
	addi %r8, %r29, 0
	li %r9, 0
2189:
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
	bne %cr0, 2189b
	b 2188f
2187:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2190:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2190b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2188:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2191f
	addi %r8, %r29, 0
2193:
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
	bne %cr0, 2193b
	b 2192f
2191:
	rldicl %r8, %r29, 63, 1
2194:
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
	bne %cr0, 2194b
2192:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2195f
	addi %r8, %r29, 0
	li %r9, 0
2197:
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
	bne %cr0, 2197b
	b 2196f
2195:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2198:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2198b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2196:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
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
	beq %cr0, 2199f
	addi %r8, %r29, 0
	li %r9, 0
2201:
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
	bne %cr0, 2201b
	b 2200f
2199:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2202:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2202b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2200:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2203f
	addi %r8, %r29, 0
2205:
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
	bne %cr0, 2205b
	b 2204f
2203:
	rldicl %r8, %r29, 63, 1
2206:
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
	bne %cr0, 2206b
2204:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2207f
	addi %r8, %r29, 0
	li %r9, 0
2209:
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
	bne %cr0, 2209b
	b 2208f
2207:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2210:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2210b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2208:
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2211f
	addi %r8, %r29, 0
2213:
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
	bne %cr0, 2213b
	b 2212f
2211:
	rldicl %r8, %r29, 63, 1
2214:
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
	bne %cr0, 2214b
2212:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2215f
	addi %r8, %r29, 0
2217:
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
	bne %cr0, 2217b
	b 2216f
2215:
	rldicl %r8, %r29, 63, 1
2218:
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
	bne %cr0, 2218b
2216:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2219f
	addi %r8, %r29, 0
2221:
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
	bne %cr0, 2221b
	b 2220f
2219:
	rldicl %r8, %r29, 63, 1
2222:
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
	bne %cr0, 2222b
2220:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2223f
	addi %r8, %r29, 0
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
2224:
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
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
	lwz %r0, 128(%r31)
	xor %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2231f
	addi %r8, %r29, 0
2233:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2233b
	b 2232f
2231:
	rldicl %r8, %r29, 63, 1
2234:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2234b
2232:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 124(%r31)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 5
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
	stw %r9, 128(%r31)
	lwz %r0, 124(%r31)
	lwz %r3, 128(%r31)
	and %r0, %r0, %r3
	stw %r0, 132(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2239f
	addi %r8, %r29, 0
	li %r9, 0
2241:
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
	bne %cr0, 2241b
	b 2240f
2239:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2242:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2242b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2240:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2243f
	addi %r8, %r29, 0
2245:
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
	bne %cr0, 2245b
	b 2244f
2243:
	rldicl %r8, %r29, 63, 1
2246:
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
	bne %cr0, 2246b
2244:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2247f
	addi %r8, %r29, 0
2249:
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
	bne %cr0, 2249b
	b 2248f
2247:
	rldicl %r8, %r29, 63, 1
2250:
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
	bne %cr0, 2250b
2248:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2251f
	addi %r8, %r29, 0
2253:
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
	bne %cr0, 2253b
	b 2252f
2251:
	rldicl %r8, %r29, 63, 1
2254:
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
	bne %cr0, 2254b
2252:
	li %r9, 0
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2255f
	addi %r8, %r29, 0
2257:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2257b
	b 2256f
2255:
	rldicl %r8, %r29, 63, 1
2258:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2258b
2256:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
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
	beq %cr0, 2259f
	addi %r8, %r29, 0
	li %r9, 0
2261:
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
	bne %cr0, 2261b
	b 2260f
2259:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2262:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2262b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2260:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2263f
	addi %r8, %r29, 0
2265:
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
	bne %cr0, 2265b
	b 2264f
2263:
	rldicl %r8, %r29, 63, 1
2266:
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
	bne %cr0, 2266b
2264:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2267f
	addi %r8, %r29, 0
	li %r9, 0
2269:
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
	bne %cr0, 2269b
	b 2268f
2267:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2270:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2270b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2268:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
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
	beq %cr0, 2271f
	addi %r8, %r29, 0
	li %r9, 0
2273:
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
	bne %cr0, 2273b
	b 2272f
2271:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2274:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2274b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2272:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2275f
	addi %r8, %r29, 0
2277:
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
	bne %cr0, 2277b
	b 2276f
2275:
	rldicl %r8, %r29, 63, 1
2278:
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
	bne %cr0, 2278b
2276:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2279f
	addi %r8, %r29, 0
	li %r9, 0
2281:
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
	bne %cr0, 2281b
	b 2280f
2279:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2282:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2282b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2280:
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2283f
	addi %r8, %r29, 0
2285:
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
	bne %cr0, 2285b
	b 2284f
2283:
	rldicl %r8, %r29, 63, 1
2286:
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
	bne %cr0, 2286b
2284:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2287f
	addi %r8, %r29, 0
2289:
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
	bne %cr0, 2289b
	b 2288f
2287:
	rldicl %r8, %r29, 63, 1
2290:
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
	bne %cr0, 2290b
2288:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2291f
	addi %r8, %r29, 0
2293:
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
	bne %cr0, 2293b
	b 2292f
2291:
	rldicl %r8, %r29, 63, 1
2294:
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
	bne %cr0, 2294b
2292:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2295f
	addi %r8, %r29, 0
2297:
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
	bne %cr0, 2297b
	b 2296f
2295:
	rldicl %r8, %r29, 63, 1
2298:
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
	bne %cr0, 2298b
2296:
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2299f
	addi %r8, %r29, 0
	li %r9, 0
2301:
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
	bne %cr0, 2301b
	b 2300f
2299:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2302:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2302b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2300:
	lwz %r0, 128(%r31)
	xor %r9, %r9, %r0
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2303f
	addi %r8, %r29, 0
2305:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2305b
	b 2304f
2303:
	rldicl %r8, %r29, 63, 1
2306:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2306b
2304:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2162b
	li %r5, 35
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 116(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2307f
	addi %r8, %r29, 0
2309:
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
	bne %cr0, 2309b
	b 2308f
2307:
	rldicl %r8, %r29, 63, 1
2310:
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
	bne %cr0, 2310b
2308:
	li %r5, 36
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 32
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2311f
	addi %r8, %r29, 0
2313:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2313b
	b 2312f
2311:
	rldicl %r8, %r29, 63, 1
2314:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2314b
2312:
	li %r5, 37
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 35
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2315f
	addi %r8, %r29, 0
2317:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2317b
	b 2316f
2315:
	rldicl %r8, %r29, 63, 1
2318:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2318b
2316:
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2319:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2319b
	rldicr %r4, %r29, 5, 58
2320:
	li %r5, 36
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2321f
	addi %r8, %r29, 0
2323:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2323b
	b 2322f
2321:
	rldicl %r8, %r29, 63, 1
2324:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2324b
2322:
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2325f
	addi %r8, %r29, 1
2327:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2327b
	b 2326f
2325:
	rldicl %r8, %r29, 63, 1
2328:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2328b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2326:
	li %r5, 39
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 38
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 37
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2329f
	addi %r8, %r29, 1
	li %r9, 0
2331:
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
	bne %cr0, 2331b
	b 2330f
2329:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2332:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2332b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2330:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 38
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 39
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2333f
	addi %r8, %r29, 1
2335:
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
	bne %cr0, 2335b
	b 2334f
2333:
	rldicl %r8, %r29, 63, 1
2336:
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
	bne %cr0, 2336b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2334:
	li %r5, 36
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2320b
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 136(%r31)
	li %r6, 21
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2337f
	addi %r8, %r29, 0
2339:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2339b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 140(%r31)
	b 2338f
2337:
	rldicl %r8, %r29, 63, 1
2340:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2340b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 140(%r31)
2338:
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2341f
	addi %r8, %r29, 0
	li %r9, 0
2343:
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
	bne %cr0, 2343b
	b 2342f
2341:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2344:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2344b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2342:
	stw %r9, 144(%r31)
	lwz %r0, 144(%r31)
	li %r3, 1
	xor %r0, %r0, %r3
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 112(%r31)
	li %r5, 40
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 112(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2345f
	addi %r8, %r29, 0
2347:
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
	bne %cr0, 2347b
	b 2346f
2345:
	rldicl %r8, %r29, 63, 1
2348:
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
	bne %cr0, 2348b
2346:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 36
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2349f
	addi %r8, %r29, 0
2351:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2351b
	b 2350f
2349:
	rldicl %r8, %r29, 63, 1
2352:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2352b
2350:
	li %r5, 37
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 40
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2353f
	addi %r8, %r29, 0
2355:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2355b
	b 2354f
2353:
	rldicl %r8, %r29, 63, 1
2356:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2356b
2354:
	li %r5, 42
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2357:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2357b
	rldicr %r4, %r29, 5, 58
2358:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2359f
	addi %r8, %r29, 0
2361:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2361b
	b 2360f
2359:
	rldicl %r8, %r29, 63, 1
2362:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2362b
2360:
	li %r5, 42
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2363f
	addi %r8, %r29, 1
2365:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2365b
	b 2364f
2363:
	rldicl %r8, %r29, 63, 1
2366:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2366b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2364:
	li %r5, 39
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 42
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 37
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2367f
	addi %r8, %r29, 1
	li %r9, 0
2369:
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
	bne %cr0, 2369b
	b 2368f
2367:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2370:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2370b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2368:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 42
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 42
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 39
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2371f
	addi %r8, %r29, 1
2373:
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
	bne %cr0, 2373b
	b 2372f
2371:
	rldicl %r8, %r29, 63, 1
2374:
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
	bne %cr0, 2374b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2372:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2358b
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 40
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2375f
	addi %r8, %r29, 0
2377:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2377b
	b 2376f
2375:
	rldicl %r8, %r29, 63, 1
2378:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2378b
2376:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 42
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2379f
	addi %r8, %r29, 0
2381:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2381b
	b 2380f
2379:
	rldicl %r8, %r29, 63, 1
2382:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2382b
2380:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2383f
	addi %r8, %r29, 0
2385:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2385b
	b 2384f
2383:
	rldicl %r8, %r29, 63, 1
2386:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2386b
2384:
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2387f
	addi %r8, %r29, 0
2389:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2389b
	b 2388f
2387:
	rldicl %r8, %r29, 63, 1
2390:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2390b
2388:
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2391f
	addi %r8, %r29, 0
2393:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2393b
	b 2392f
2391:
	rldicl %r8, %r29, 63, 1
2394:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2394b
2392:
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 8
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2395f
	addi %r8, %r29, 0
	li %r9, 0
2397:
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
	bne %cr0, 2397b
	b 2396f
2395:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2398:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2398b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2396:
	rldicr %r4, %r29, 5, 58
2399:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 124(%r31)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 2400f
	addi %r8, %r29, 0
	li %r9, 0
2402:
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
	bne %cr0, 2402b
	b 2401f
2400:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2403:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2403b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2401:
	stw %r9, 128(%r31)
	lwz %r0, 124(%r31)
	lwz %r3, 128(%r31)
	and %r0, %r0, %r3
	stw %r0, 132(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 0
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2404f
	addi %r8, %r29, 0
	li %r9, 0
2406:
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
	bne %cr0, 2406b
	b 2405f
2404:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2407:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2407b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2405:
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 0
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2408f
	addi %r8, %r29, 0
2410:
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
	bne %cr0, 2410b
	b 2409f
2408:
	rldicl %r8, %r29, 63, 1
2411:
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
	bne %cr0, 2411b
2409:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2412f
	addi %r8, %r29, 0
2414:
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
	bne %cr0, 2414b
	b 2413f
2412:
	rldicl %r8, %r29, 63, 1
2415:
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
	bne %cr0, 2415b
2413:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2416f
	addi %r8, %r29, 0
2418:
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
	bne %cr0, 2418b
	b 2417f
2416:
	rldicl %r8, %r29, 63, 1
2419:
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
	bne %cr0, 2419b
2417:
	li %r9, 0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2420f
	addi %r8, %r29, 0
2422:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2422b
	b 2421f
2420:
	rldicl %r8, %r29, 63, 1
2423:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2423b
2421:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
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
	beq %cr0, 2424f
	addi %r8, %r29, 0
	li %r9, 0
2426:
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
	bne %cr0, 2426b
	b 2425f
2424:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2427:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2427b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2425:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2428f
	addi %r8, %r29, 0
2430:
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
	bne %cr0, 2430b
	b 2429f
2428:
	rldicl %r8, %r29, 63, 1
2431:
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
	bne %cr0, 2431b
2429:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2432f
	addi %r8, %r29, 0
	li %r9, 0
2434:
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
	bne %cr0, 2434b
	b 2433f
2432:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2435:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2435b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2433:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
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
	beq %cr0, 2436f
	addi %r8, %r29, 0
	li %r9, 0
2438:
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
	bne %cr0, 2438b
	b 2437f
2436:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2439:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2439b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2437:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2440f
	addi %r8, %r29, 0
2442:
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
	bne %cr0, 2442b
	b 2441f
2440:
	rldicl %r8, %r29, 63, 1
2443:
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
	bne %cr0, 2443b
2441:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2444f
	addi %r8, %r29, 0
	li %r9, 0
2446:
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
	bne %cr0, 2446b
	b 2445f
2444:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2447:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2447b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2445:
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2448f
	addi %r8, %r29, 0
2450:
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
	bne %cr0, 2450b
	b 2449f
2448:
	rldicl %r8, %r29, 63, 1
2451:
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
	bne %cr0, 2451b
2449:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2452f
	addi %r8, %r29, 0
2454:
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
	bne %cr0, 2454b
	b 2453f
2452:
	rldicl %r8, %r29, 63, 1
2455:
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
	bne %cr0, 2455b
2453:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2456f
	addi %r8, %r29, 0
2458:
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
	bne %cr0, 2458b
	b 2457f
2456:
	rldicl %r8, %r29, 63, 1
2459:
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
	bne %cr0, 2459b
2457:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2460f
	addi %r8, %r29, 0
2462:
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
	bne %cr0, 2462b
	b 2461f
2460:
	rldicl %r8, %r29, 63, 1
2463:
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
	bne %cr0, 2463b
2461:
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2464f
	addi %r8, %r29, 0
	li %r9, 0
2466:
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
	bne %cr0, 2466b
	b 2465f
2464:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2467:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2467b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2465:
	lwz %r0, 128(%r31)
	xor %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2468f
	addi %r8, %r29, 0
2470:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2470b
	b 2469f
2468:
	rldicl %r8, %r29, 63, 1
2471:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2471b
2469:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 124(%r31)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 5
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2472f
	addi %r8, %r29, 0
	li %r9, 0
2474:
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
	bne %cr0, 2474b
	b 2473f
2472:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2475:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2475b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2473:
	stw %r9, 128(%r31)
	lwz %r0, 124(%r31)
	lwz %r3, 128(%r31)
	and %r0, %r0, %r3
	stw %r0, 132(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2476f
	addi %r8, %r29, 0
	li %r9, 0
2478:
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
	bne %cr0, 2478b
	b 2477f
2476:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2479:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2479b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2477:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2480f
	addi %r8, %r29, 0
2482:
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
	bne %cr0, 2482b
	b 2481f
2480:
	rldicl %r8, %r29, 63, 1
2483:
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
	bne %cr0, 2483b
2481:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2484f
	addi %r8, %r29, 0
2486:
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
	bne %cr0, 2486b
	b 2485f
2484:
	rldicl %r8, %r29, 63, 1
2487:
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
	bne %cr0, 2487b
2485:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2488f
	addi %r8, %r29, 0
2490:
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
	bne %cr0, 2490b
	b 2489f
2488:
	rldicl %r8, %r29, 63, 1
2491:
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
	bne %cr0, 2491b
2489:
	li %r9, 0
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2492f
	addi %r8, %r29, 0
2494:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2494b
	b 2493f
2492:
	rldicl %r8, %r29, 63, 1
2495:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2495b
2493:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
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
	beq %cr0, 2496f
	addi %r8, %r29, 0
	li %r9, 0
2498:
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
	bne %cr0, 2498b
	b 2497f
2496:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2499:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2499b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2497:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2500f
	addi %r8, %r29, 0
2502:
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
	bne %cr0, 2502b
	b 2501f
2500:
	rldicl %r8, %r29, 63, 1
2503:
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
	bne %cr0, 2503b
2501:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2504f
	addi %r8, %r29, 0
	li %r9, 0
2506:
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
	bne %cr0, 2506b
	b 2505f
2504:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2507:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2507b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2505:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
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
	beq %cr0, 2508f
	addi %r8, %r29, 0
	li %r9, 0
2510:
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
	bne %cr0, 2510b
	b 2509f
2508:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2511:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2511b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2509:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2512f
	addi %r8, %r29, 0
2514:
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
	bne %cr0, 2514b
	b 2513f
2512:
	rldicl %r8, %r29, 63, 1
2515:
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
	bne %cr0, 2515b
2513:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2516f
	addi %r8, %r29, 0
	li %r9, 0
2518:
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
	bne %cr0, 2518b
	b 2517f
2516:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2519:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2519b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2517:
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2520f
	addi %r8, %r29, 0
2522:
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
	bne %cr0, 2522b
	b 2521f
2520:
	rldicl %r8, %r29, 63, 1
2523:
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
	bne %cr0, 2523b
2521:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2524f
	addi %r8, %r29, 0
2526:
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
	bne %cr0, 2526b
	b 2525f
2524:
	rldicl %r8, %r29, 63, 1
2527:
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
	bne %cr0, 2527b
2525:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2528f
	addi %r8, %r29, 0
2530:
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
	bne %cr0, 2530b
	b 2529f
2528:
	rldicl %r8, %r29, 63, 1
2531:
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
	bne %cr0, 2531b
2529:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2532f
	addi %r8, %r29, 0
2534:
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
	bne %cr0, 2534b
	b 2533f
2532:
	rldicl %r8, %r29, 63, 1
2535:
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
	bne %cr0, 2535b
2533:
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2536f
	addi %r8, %r29, 0
	li %r9, 0
2538:
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
	bne %cr0, 2538b
	b 2537f
2536:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2539:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2539b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2537:
	lwz %r0, 128(%r31)
	xor %r9, %r9, %r0
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2540f
	addi %r8, %r29, 0
2542:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2542b
	b 2541f
2540:
	rldicl %r8, %r29, 63, 1
2543:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2543b
2541:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2399b
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2544f
	addi %r8, %r29, 0
2546:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2546b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 116(%r31)
	b 2545f
2544:
	rldicl %r8, %r29, 63, 1
2547:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2547b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 116(%r31)
2545:
	li %r5, 43
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 40
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
	beq %cr0, 2548f
	addi %r8, %r29, 0
	li %r9, 0
2550:
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
	bne %cr0, 2550b
	b 2549f
2548:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2551:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2551b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2549:
	li %r5, 56
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 41
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2552f
	addi %r8, %r29, 0
2554:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2554b
	b 2553f
2552:
	rldicl %r8, %r29, 63, 1
2555:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2555b
2553:
	li %r5, 57
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 43
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2556f
	addi %r8, %r29, 0
2558:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2558b
	b 2557f
2556:
	rldicl %r8, %r29, 63, 1
2559:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2559b
2557:
	li %r5, 55
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2560f
	addi %r8, %r29, 0
2562:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2562b
	b 2561f
2560:
	rldicl %r8, %r29, 63, 1
2563:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2563b
2561:
	li %r11, 64
2564:
	li %r5, 57
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 124(%r31)
	li %r5, 58
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 56
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2565f
	addi %r8, %r29, 0
2567:
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
	bne %cr0, 2567b
	b 2566f
2565:
	rldicl %r8, %r29, 63, 1
2568:
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
	bne %cr0, 2568b
2566:
	li %r5, 59
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 58
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2569f
	addi %r8, %r29, 0
	li %r9, 0
2571:
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
	bne %cr0, 2571b
	b 2570f
2569:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2572:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2572b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2570:
	li %r5, 55
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 55
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 59
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2573f
	addi %r8, %r29, 0
	li %r9, 0
2575:
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
	bne %cr0, 2575b
	b 2574f
2573:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2576:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2576b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2574:
	li %r5, 59
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 56
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2577f
	addi %r8, %r29, 0
	li %r9, 0
2579:
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
	bne %cr0, 2579b
	b 2578f
2577:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2580:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2580b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2578:
	li %r5, 56
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 56
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 59
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2581f
	addi %r8, %r29, 0
	li %r9, 0
2583:
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
	bne %cr0, 2583b
	b 2582f
2581:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2584:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2584b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2582:
	li %r9, 0
	li %r5, 57
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2585f
	addi %r8, %r29, 0
2587:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2587b
	b 2586f
2585:
	rldicl %r8, %r29, 63, 1
2588:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2588b
2586:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 2564b
	li %r5, 44
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 55
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2589f
	addi %r8, %r29, 0
2591:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2591b
	b 2590f
2589:
	rldicl %r8, %r29, 63, 1
2592:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2592b
2590:
	li %r5, 56
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 42
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2593f
	addi %r8, %r29, 0
2595:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2595b
	b 2594f
2593:
	rldicl %r8, %r29, 63, 1
2596:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2596b
2594:
	li %r5, 57
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 43
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2597f
	addi %r8, %r29, 0
2599:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2599b
	b 2598f
2597:
	rldicl %r8, %r29, 63, 1
2600:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2600b
2598:
	li %r5, 55
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2601f
	addi %r8, %r29, 0
2603:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2603b
	b 2602f
2601:
	rldicl %r8, %r29, 63, 1
2604:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2604b
2602:
	li %r11, 64
2605:
	li %r5, 57
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 124(%r31)
	li %r5, 58
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 56
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2606f
	addi %r8, %r29, 0
2608:
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
	bne %cr0, 2608b
	b 2607f
2606:
	rldicl %r8, %r29, 63, 1
2609:
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
	bne %cr0, 2609b
2607:
	li %r5, 59
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 58
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2610f
	addi %r8, %r29, 0
	li %r9, 0
2612:
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
	bne %cr0, 2612b
	b 2611f
2610:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2613:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2613b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2611:
	li %r5, 55
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 55
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 59
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2614f
	addi %r8, %r29, 0
	li %r9, 0
2616:
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
	bne %cr0, 2616b
	b 2615f
2614:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2617:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2617b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2615:
	li %r5, 59
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 56
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2618f
	addi %r8, %r29, 0
	li %r9, 0
2620:
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
	bne %cr0, 2620b
	b 2619f
2618:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2621:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2621b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2619:
	li %r5, 56
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 56
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 59
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2622f
	addi %r8, %r29, 0
	li %r9, 0
2624:
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
	bne %cr0, 2624b
	b 2623f
2622:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2625:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2625b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2623:
	li %r9, 0
	li %r5, 57
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2626f
	addi %r8, %r29, 0
2628:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2628b
	b 2627f
2626:
	rldicl %r8, %r29, 63, 1
2629:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2629b
2627:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 2605b
	li %r5, 45
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 55
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2630f
	addi %r8, %r29, 0
2632:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2632b
	b 2631f
2630:
	rldicl %r8, %r29, 63, 1
2633:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2633b
2631:
	li %r5, 46
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2634f
	addi %r8, %r29, 0
	li %r9, 0
2636:
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
	bne %cr0, 2636b
	b 2635f
2634:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2637:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2637b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2635:
	li %r5, 45
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 45
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 46
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2638f
	addi %r8, %r29, 0
	li %r9, 0
2640:
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
	bne %cr0, 2640b
	b 2639f
2638:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2641:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2641b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2639:
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2642:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2642b
	rldicr %r4, %r29, 5, 58
2643:
	li %r5, 45
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2644f
	addi %r8, %r29, 0
2646:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2646b
	b 2645f
2644:
	rldicl %r8, %r29, 63, 1
2647:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2647b
2645:
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2648f
	addi %r8, %r29, 1
2650:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2650b
	b 2649f
2648:
	rldicl %r8, %r29, 63, 1
2651:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2651b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2649:
	li %r5, 39
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 38
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 37
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2652f
	addi %r8, %r29, 1
	li %r9, 0
2654:
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
	bne %cr0, 2654b
	b 2653f
2652:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2655:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2655b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2653:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 38
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 39
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2656f
	addi %r8, %r29, 1
2658:
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
	bne %cr0, 2658b
	b 2657f
2656:
	rldicl %r8, %r29, 63, 1
2659:
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
	bne %cr0, 2659b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2657:
	li %r5, 45
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2643b
	li %r5, 47
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 44
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2660f
	addi %r8, %r29, 0
2662:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2662b
	b 2661f
2660:
	rldicl %r8, %r29, 63, 1
2663:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2663b
2661:
	li %r5, 46
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 45
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2664f
	addi %r8, %r29, 0
	li %r9, 0
2666:
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
	bne %cr0, 2666b
	b 2665f
2664:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2667:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2667b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2665:
	li %r5, 47
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 47
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 46
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2668f
	addi %r8, %r29, 0
	li %r9, 0
2670:
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
	bne %cr0, 2670b
	b 2669f
2668:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2671:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2671b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2669:
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 36
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 16
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2672f
	addi %r8, %r29, 0
	li %r9, 0
2674:
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
	bne %cr0, 2674b
	b 2673f
2672:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2675:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2675b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2673:
	stw %r9, 120(%r31)
	lwz %r0, 120(%r31)
	li %r3, 1
	xor %r0, %r0, %r3
	lwz %r3, 116(%r31)
	and %r0, %r0, %r3
	stw %r0, 148(%r31)
	li %r6, 36
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2676f
	addi %r8, %r29, 0
2678:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2678b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 112(%r31)
	b 2677f
2676:
	rldicl %r8, %r29, 63, 1
2679:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2679b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 112(%r31)
2677:
	lwz %r0, 112(%r31)
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 152(%r31)
	lwz %r0, 148(%r31)
	lwz %r3, 152(%r31)
	xor %r3, %r3, %r0
	lwz %r9, 140(%r31)
	and %r3, %r3, %r9
	xor %r0, %r0, %r3
	stw %r0, 148(%r31)
	li %r5, 29
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 47
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 140(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2680f
	addi %r8, %r29, 0
2682:
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
	bne %cr0, 2682b
	b 2681f
2680:
	rldicl %r8, %r29, 63, 1
2683:
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
	bne %cr0, 2683b
2681:
	li %r5, 36
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 112(%r31)
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 36
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2684f
	addi %r8, %r29, 0
	li %r9, 0
2686:
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
	bne %cr0, 2686b
	b 2685f
2684:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2687:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2687b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2685:
	stw %r9, 116(%r31)
	lwz %r0, 116(%r31)
	li %r3, 1
	xor %r0, %r0, %r3
	lwz %r3, 112(%r31)
	and %r0, %r0, %r3
	stw %r0, 120(%r31)
	li %r5, 48
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 36
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 120(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2688f
	addi %r8, %r29, 0
2690:
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
	bne %cr0, 2690b
	b 2689f
2688:
	rldicl %r8, %r29, 63, 1
2691:
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
	bne %cr0, 2691b
2689:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 48
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2692f
	addi %r8, %r29, 0
2694:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2694b
	b 2693f
2692:
	rldicl %r8, %r29, 63, 1
2695:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2695b
2693:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2696f
	addi %r8, %r29, 0
2698:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2698b
	b 2697f
2696:
	rldicl %r8, %r29, 63, 1
2699:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2699b
2697:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2700f
	addi %r8, %r29, 0
2702:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2702b
	b 2701f
2700:
	rldicl %r8, %r29, 63, 1
2703:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2703b
2701:
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2704f
	addi %r8, %r29, 0
2706:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2706b
	b 2705f
2704:
	rldicl %r8, %r29, 63, 1
2707:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2707b
2705:
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2708f
	addi %r8, %r29, 0
2710:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2710b
	b 2709f
2708:
	rldicl %r8, %r29, 63, 1
2711:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2711b
2709:
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 8
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2712f
	addi %r8, %r29, 0
	li %r9, 0
2714:
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
	bne %cr0, 2714b
	b 2713f
2712:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2715:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2715b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2713:
	rldicr %r4, %r29, 5, 58
2716:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 124(%r31)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 2717f
	addi %r8, %r29, 0
	li %r9, 0
2719:
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
	bne %cr0, 2719b
	b 2718f
2717:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2720:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2720b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2718:
	stw %r9, 128(%r31)
	lwz %r0, 124(%r31)
	lwz %r3, 128(%r31)
	and %r0, %r0, %r3
	stw %r0, 132(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 0
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2721f
	addi %r8, %r29, 0
	li %r9, 0
2723:
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
	bne %cr0, 2723b
	b 2722f
2721:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2724:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2724b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2722:
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 0
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2725f
	addi %r8, %r29, 0
2727:
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
	bne %cr0, 2727b
	b 2726f
2725:
	rldicl %r8, %r29, 63, 1
2728:
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
	bne %cr0, 2728b
2726:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2729f
	addi %r8, %r29, 0
2731:
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
	bne %cr0, 2731b
	b 2730f
2729:
	rldicl %r8, %r29, 63, 1
2732:
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
	bne %cr0, 2732b
2730:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2733f
	addi %r8, %r29, 0
2735:
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
	bne %cr0, 2735b
	b 2734f
2733:
	rldicl %r8, %r29, 63, 1
2736:
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
	bne %cr0, 2736b
2734:
	li %r9, 0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2737f
	addi %r8, %r29, 0
2739:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2739b
	b 2738f
2737:
	rldicl %r8, %r29, 63, 1
2740:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2740b
2738:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
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
	beq %cr0, 2741f
	addi %r8, %r29, 0
	li %r9, 0
2743:
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
	bne %cr0, 2743b
	b 2742f
2741:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2744:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2744b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2742:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2745f
	addi %r8, %r29, 0
2747:
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
	bne %cr0, 2747b
	b 2746f
2745:
	rldicl %r8, %r29, 63, 1
2748:
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
	bne %cr0, 2748b
2746:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2749f
	addi %r8, %r29, 0
	li %r9, 0
2751:
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
	bne %cr0, 2751b
	b 2750f
2749:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2752:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2752b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2750:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
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
	beq %cr0, 2753f
	addi %r8, %r29, 0
	li %r9, 0
2755:
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
	bne %cr0, 2755b
	b 2754f
2753:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2756:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2756b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2754:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2757f
	addi %r8, %r29, 0
2759:
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
	bne %cr0, 2759b
	b 2758f
2757:
	rldicl %r8, %r29, 63, 1
2760:
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
	bne %cr0, 2760b
2758:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2761f
	addi %r8, %r29, 0
	li %r9, 0
2763:
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
	bne %cr0, 2763b
	b 2762f
2761:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2764:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2764b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2762:
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2765f
	addi %r8, %r29, 0
2767:
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
	bne %cr0, 2767b
	b 2766f
2765:
	rldicl %r8, %r29, 63, 1
2768:
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
	bne %cr0, 2768b
2766:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2769f
	addi %r8, %r29, 0
2771:
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
	bne %cr0, 2771b
	b 2770f
2769:
	rldicl %r8, %r29, 63, 1
2772:
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
	bne %cr0, 2772b
2770:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2773f
	addi %r8, %r29, 0
2775:
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
	bne %cr0, 2775b
	b 2774f
2773:
	rldicl %r8, %r29, 63, 1
2776:
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
	bne %cr0, 2776b
2774:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2777f
	addi %r8, %r29, 0
2779:
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
	bne %cr0, 2779b
	b 2778f
2777:
	rldicl %r8, %r29, 63, 1
2780:
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
	bne %cr0, 2780b
2778:
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2781f
	addi %r8, %r29, 0
	li %r9, 0
2783:
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
	bne %cr0, 2783b
	b 2782f
2781:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2784:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2784b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2782:
	lwz %r0, 128(%r31)
	xor %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2785f
	addi %r8, %r29, 0
2787:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2787b
	b 2786f
2785:
	rldicl %r8, %r29, 63, 1
2788:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2788b
2786:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 124(%r31)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 5
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2789f
	addi %r8, %r29, 0
	li %r9, 0
2791:
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
	bne %cr0, 2791b
	b 2790f
2789:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2792:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2792b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2790:
	stw %r9, 128(%r31)
	lwz %r0, 124(%r31)
	lwz %r3, 128(%r31)
	and %r0, %r0, %r3
	stw %r0, 132(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2793f
	addi %r8, %r29, 0
	li %r9, 0
2795:
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
	bne %cr0, 2795b
	b 2794f
2793:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2796:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2796b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2794:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2797f
	addi %r8, %r29, 0
2799:
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
	bne %cr0, 2799b
	b 2798f
2797:
	rldicl %r8, %r29, 63, 1
2800:
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
	bne %cr0, 2800b
2798:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2801f
	addi %r8, %r29, 0
2803:
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
	bne %cr0, 2803b
	b 2802f
2801:
	rldicl %r8, %r29, 63, 1
2804:
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
	bne %cr0, 2804b
2802:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2805f
	addi %r8, %r29, 0
2807:
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
	bne %cr0, 2807b
	b 2806f
2805:
	rldicl %r8, %r29, 63, 1
2808:
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
	bne %cr0, 2808b
2806:
	li %r9, 0
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2809f
	addi %r8, %r29, 0
2811:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2811b
	b 2810f
2809:
	rldicl %r8, %r29, 63, 1
2812:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2812b
2810:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
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
	beq %cr0, 2813f
	addi %r8, %r29, 0
	li %r9, 0
2815:
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
	bne %cr0, 2815b
	b 2814f
2813:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2816:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2816b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2814:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2817f
	addi %r8, %r29, 0
2819:
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
	bne %cr0, 2819b
	b 2818f
2817:
	rldicl %r8, %r29, 63, 1
2820:
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
	bne %cr0, 2820b
2818:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2821f
	addi %r8, %r29, 0
	li %r9, 0
2823:
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
	bne %cr0, 2823b
	b 2822f
2821:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2824:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2824b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2822:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
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
	beq %cr0, 2825f
	addi %r8, %r29, 0
	li %r9, 0
2827:
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
	bne %cr0, 2827b
	b 2826f
2825:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2828:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2828b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2826:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2829f
	addi %r8, %r29, 0
2831:
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
	bne %cr0, 2831b
	b 2830f
2829:
	rldicl %r8, %r29, 63, 1
2832:
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
	bne %cr0, 2832b
2830:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2833f
	addi %r8, %r29, 0
	li %r9, 0
2835:
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
	bne %cr0, 2835b
	b 2834f
2833:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2836:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2836b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2834:
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2837f
	addi %r8, %r29, 0
2839:
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
	bne %cr0, 2839b
	b 2838f
2837:
	rldicl %r8, %r29, 63, 1
2840:
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
	bne %cr0, 2840b
2838:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2841f
	addi %r8, %r29, 0
2843:
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
	bne %cr0, 2843b
	b 2842f
2841:
	rldicl %r8, %r29, 63, 1
2844:
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
	bne %cr0, 2844b
2842:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2845f
	addi %r8, %r29, 0
2847:
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
	bne %cr0, 2847b
	b 2846f
2845:
	rldicl %r8, %r29, 63, 1
2848:
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
	bne %cr0, 2848b
2846:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2849f
	addi %r8, %r29, 0
2851:
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
	bne %cr0, 2851b
	b 2850f
2849:
	rldicl %r8, %r29, 63, 1
2852:
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
	bne %cr0, 2852b
2850:
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2853f
	addi %r8, %r29, 0
	li %r9, 0
2855:
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
	bne %cr0, 2855b
	b 2854f
2853:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2856:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2856b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2854:
	lwz %r0, 128(%r31)
	xor %r9, %r9, %r0
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2857f
	addi %r8, %r29, 0
2859:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2859b
	b 2858f
2857:
	rldicl %r8, %r29, 63, 1
2860:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2860b
2858:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2716b
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2861f
	addi %r8, %r29, 0
2863:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2863b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 112(%r31)
	b 2862f
2861:
	rldicl %r8, %r29, 63, 1
2864:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2864b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 112(%r31)
2862:
	lwz %r0, 120(%r31)
	lwz %r3, 112(%r31)
	and %r0, %r0, %r3
	stw %r0, 116(%r31)
	lwz %r0, 116(%r31)
	lwz %r3, 148(%r31)
	xor %r3, %r3, %r0
	lwz %r9, 136(%r31)
	and %r3, %r3, %r9
	xor %r0, %r0, %r3
	stw %r0, 148(%r31)
	li %r5, 49
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 29
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 136(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2865f
	addi %r8, %r29, 0
2867:
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
	bne %cr0, 2867b
	b 2866f
2865:
	rldicl %r8, %r29, 63, 1
2868:
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
	bne %cr0, 2868b
2866:
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 49
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 19
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2869f
	addi %r8, %r29, 0
	li %r9, 0
2871:
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
	bne %cr0, 2871b
	b 2870f
2869:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2872:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2872b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2870:
	stw %r9, 112(%r31)
	lwz %r0, 112(%r31)
	lwz %r3, 148(%r31)
	and %r0, %r0, %r3
	stw %r0, 152(%r31)
	li %r5, 24
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 112(%r31)
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 24
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2873f
	addi %r8, %r29, 0
	li %r9, 0
2875:
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
	bne %cr0, 2875b
	b 2874f
2873:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2876:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2876b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2874:
	stw %r9, 116(%r31)
	lwz %r0, 116(%r31)
	li %r3, 1
	xor %r0, %r0, %r3
	lwz %r3, 112(%r31)
	and %r0, %r0, %r3
	stw %r0, 120(%r31)
	li %r5, 54
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 24
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 120(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2877f
	addi %r8, %r29, 0
2879:
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
	bne %cr0, 2879b
	b 2878f
2877:
	rldicl %r8, %r29, 63, 1
2880:
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
	bne %cr0, 2880b
2878:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 54
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2881f
	addi %r8, %r29, 0
2883:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2883b
	b 2882f
2881:
	rldicl %r8, %r29, 63, 1
2884:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2884b
2882:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 25
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2885f
	addi %r8, %r29, 0
2887:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2887b
	b 2886f
2885:
	rldicl %r8, %r29, 63, 1
2888:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2888b
2886:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2889f
	addi %r8, %r29, 0
2891:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2891b
	b 2890f
2889:
	rldicl %r8, %r29, 63, 1
2892:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2892b
2890:
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 15
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2893f
	addi %r8, %r29, 0
2895:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2895b
	b 2894f
2893:
	rldicl %r8, %r29, 63, 1
2896:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2896b
2894:
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2897f
	addi %r8, %r29, 0
2899:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2899b
	b 2898f
2897:
	rldicl %r8, %r29, 63, 1
2900:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2900b
2898:
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 8
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2901f
	addi %r8, %r29, 0
	li %r9, 0
2903:
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
	bne %cr0, 2903b
	b 2902f
2901:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2904:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2904b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2902:
	rldicr %r4, %r29, 5, 58
2905:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 124(%r31)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 2906f
	addi %r8, %r29, 0
	li %r9, 0
2908:
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
	bne %cr0, 2908b
	b 2907f
2906:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2909:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2909b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2907:
	stw %r9, 128(%r31)
	lwz %r0, 124(%r31)
	lwz %r3, 128(%r31)
	and %r0, %r0, %r3
	stw %r0, 132(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 0
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2910f
	addi %r8, %r29, 0
	li %r9, 0
2912:
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
	bne %cr0, 2912b
	b 2911f
2910:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2913:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2913b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2911:
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 0
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2914f
	addi %r8, %r29, 0
2916:
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
	bne %cr0, 2916b
	b 2915f
2914:
	rldicl %r8, %r29, 63, 1
2917:
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
	bne %cr0, 2917b
2915:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2918f
	addi %r8, %r29, 0
2920:
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
	bne %cr0, 2920b
	b 2919f
2918:
	rldicl %r8, %r29, 63, 1
2921:
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
	bne %cr0, 2921b
2919:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2922f
	addi %r8, %r29, 0
2924:
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
	bne %cr0, 2924b
	b 2923f
2922:
	rldicl %r8, %r29, 63, 1
2925:
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
	bne %cr0, 2925b
2923:
	li %r9, 0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2926f
	addi %r8, %r29, 0
2928:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2928b
	b 2927f
2926:
	rldicl %r8, %r29, 63, 1
2929:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2929b
2927:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
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
	beq %cr0, 2930f
	addi %r8, %r29, 0
	li %r9, 0
2932:
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
	bne %cr0, 2932b
	b 2931f
2930:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2933:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2933b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2931:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2934f
	addi %r8, %r29, 0
2936:
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
	bne %cr0, 2936b
	b 2935f
2934:
	rldicl %r8, %r29, 63, 1
2937:
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
	bne %cr0, 2937b
2935:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2938f
	addi %r8, %r29, 0
	li %r9, 0
2940:
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
	bne %cr0, 2940b
	b 2939f
2938:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2941:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2941b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2939:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
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
	beq %cr0, 2942f
	addi %r8, %r29, 0
	li %r9, 0
2944:
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
	bne %cr0, 2944b
	b 2943f
2942:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2945:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2945b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2943:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2946f
	addi %r8, %r29, 0
2948:
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
	bne %cr0, 2948b
	b 2947f
2946:
	rldicl %r8, %r29, 63, 1
2949:
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
	bne %cr0, 2949b
2947:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2950f
	addi %r8, %r29, 0
	li %r9, 0
2952:
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
	bne %cr0, 2952b
	b 2951f
2950:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2953:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2953b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2951:
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2954f
	addi %r8, %r29, 0
2956:
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
	bne %cr0, 2956b
	b 2955f
2954:
	rldicl %r8, %r29, 63, 1
2957:
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
	bne %cr0, 2957b
2955:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2958f
	addi %r8, %r29, 0
2960:
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
	bne %cr0, 2960b
	b 2959f
2958:
	rldicl %r8, %r29, 63, 1
2961:
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
	bne %cr0, 2961b
2959:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2962f
	addi %r8, %r29, 0
2964:
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
	bne %cr0, 2964b
	b 2963f
2962:
	rldicl %r8, %r29, 63, 1
2965:
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
	bne %cr0, 2965b
2963:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2966f
	addi %r8, %r29, 0
2968:
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
	bne %cr0, 2968b
	b 2967f
2966:
	rldicl %r8, %r29, 63, 1
2969:
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
	bne %cr0, 2969b
2967:
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2970f
	addi %r8, %r29, 0
	li %r9, 0
2972:
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
	bne %cr0, 2972b
	b 2971f
2970:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2973:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2973b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2971:
	lwz %r0, 128(%r31)
	xor %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2974f
	addi %r8, %r29, 0
2976:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2976b
	b 2975f
2974:
	rldicl %r8, %r29, 63, 1
2977:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2977b
2975:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 124(%r31)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 5
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2978f
	addi %r8, %r29, 0
	li %r9, 0
2980:
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
	bne %cr0, 2980b
	b 2979f
2978:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2981:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2981b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2979:
	stw %r9, 128(%r31)
	lwz %r0, 124(%r31)
	lwz %r3, 128(%r31)
	and %r0, %r0, %r3
	stw %r0, 132(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2982f
	addi %r8, %r29, 0
	li %r9, 0
2984:
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
	bne %cr0, 2984b
	b 2983f
2982:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2985:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2985b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2983:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2986f
	addi %r8, %r29, 0
2988:
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
	bne %cr0, 2988b
	b 2987f
2986:
	rldicl %r8, %r29, 63, 1
2989:
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
	bne %cr0, 2989b
2987:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2990f
	addi %r8, %r29, 0
2992:
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
	bne %cr0, 2992b
	b 2991f
2990:
	rldicl %r8, %r29, 63, 1
2993:
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
	bne %cr0, 2993b
2991:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2994f
	addi %r8, %r29, 0
2996:
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
	bne %cr0, 2996b
	b 2995f
2994:
	rldicl %r8, %r29, 63, 1
2997:
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
	bne %cr0, 2997b
2995:
	li %r9, 0
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2998f
	addi %r8, %r29, 0
21000:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21000b
	b 2999f
2998:
	rldicl %r8, %r29, 63, 1
21001:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21001b
2999:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
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
	beq %cr0, 21002f
	addi %r8, %r29, 0
	li %r9, 0
21004:
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
	bne %cr0, 21004b
	b 21003f
21002:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
21005:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21005b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
21003:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21006f
	addi %r8, %r29, 0
21008:
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
	bne %cr0, 21008b
	b 21007f
21006:
	rldicl %r8, %r29, 63, 1
21009:
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
	bne %cr0, 21009b
21007:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21010f
	addi %r8, %r29, 0
	li %r9, 0
21012:
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
	bne %cr0, 21012b
	b 21011f
21010:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
21013:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21013b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
21011:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
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
	beq %cr0, 21014f
	addi %r8, %r29, 0
	li %r9, 0
21016:
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
	bne %cr0, 21016b
	b 21015f
21014:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
21017:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21017b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
21015:
	stw %r9, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21018f
	addi %r8, %r29, 0
21020:
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
	bne %cr0, 21020b
	b 21019f
21018:
	rldicl %r8, %r29, 63, 1
21021:
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
	bne %cr0, 21021b
21019:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21022f
	addi %r8, %r29, 0
	li %r9, 0
21024:
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
	bne %cr0, 21024b
	b 21023f
21022:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
21025:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21025b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
21023:
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21026f
	addi %r8, %r29, 0
21028:
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
	bne %cr0, 21028b
	b 21027f
21026:
	rldicl %r8, %r29, 63, 1
21029:
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
	bne %cr0, 21029b
21027:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 12
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21030f
	addi %r8, %r29, 0
21032:
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
	bne %cr0, 21032b
	b 21031f
21030:
	rldicl %r8, %r29, 63, 1
21033:
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
	bne %cr0, 21033b
21031:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21034f
	addi %r8, %r29, 0
21036:
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
	bne %cr0, 21036b
	b 21035f
21034:
	rldicl %r8, %r29, 63, 1
21037:
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
	bne %cr0, 21037b
21035:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 9
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21038f
	addi %r8, %r29, 0
21040:
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
	bne %cr0, 21040b
	b 21039f
21038:
	rldicl %r8, %r29, 63, 1
21041:
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
	bne %cr0, 21041b
21039:
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 14
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21042f
	addi %r8, %r29, 0
	li %r9, 0
21044:
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
	bne %cr0, 21044b
	b 21043f
21042:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
21045:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21045b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
21043:
	lwz %r0, 128(%r31)
	xor %r9, %r9, %r0
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21046f
	addi %r8, %r29, 0
21048:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21048b
	b 21047f
21046:
	rldicl %r8, %r29, 63, 1
21049:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21049b
21047:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2905b
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21050f
	addi %r8, %r29, 0
21052:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21052b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 116(%r31)
	b 21051f
21050:
	rldicl %r8, %r29, 63, 1
21053:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21053b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 116(%r31)
21051:
	li %r5, 52
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21054f
	addi %r8, %r29, 0
21056:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21056b
	b 21055f
21054:
	rldicl %r8, %r29, 63, 1
21057:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21057b
21055:
	li %r6, 26
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 10
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21058f
	addi %r8, %r29, 0
21060:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21060b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 120(%r31)
	b 21059f
21058:
	rldicl %r8, %r29, 63, 1
21061:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21061b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 120(%r31)
21059:
	li %r5, 29
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 26
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 120(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21062f
	addi %r8, %r29, 0
21064:
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
	bne %cr0, 21064b
	b 21063f
21062:
	rldicl %r8, %r29, 63, 1
21065:
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
	bne %cr0, 21065b
21063:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 49
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21066f
	addi %r8, %r29, 0
21068:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21068b
	b 21067f
21066:
	rldicl %r8, %r29, 63, 1
21069:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21069b
21067:
	li %r5, 37
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 29
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21070f
	addi %r8, %r29, 0
21072:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21072b
	b 21071f
21070:
	rldicl %r8, %r29, 63, 1
21073:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21073b
21071:
	li %r5, 50
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
21074:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21074b
	rldicr %r4, %r29, 5, 58
21075:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21076f
	addi %r8, %r29, 0
21078:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21078b
	b 21077f
21076:
	rldicl %r8, %r29, 63, 1
21079:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21079b
21077:
	li %r5, 50
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21080f
	addi %r8, %r29, 1
21082:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21082b
	b 21081f
21080:
	rldicl %r8, %r29, 63, 1
21083:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21083b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
21081:
	li %r5, 39
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 50
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 37
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21084f
	addi %r8, %r29, 1
	li %r9, 0
21086:
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
	bne %cr0, 21086b
	b 21085f
21084:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
21087:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21087b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
21085:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 50
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 50
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 39
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21088f
	addi %r8, %r29, 1
21090:
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
	bne %cr0, 21090b
	b 21089f
21088:
	rldicl %r8, %r29, 63, 1
21091:
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
	bne %cr0, 21091b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
21089:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 21075b
	li %r6, 27
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 10
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21092f
	addi %r8, %r29, 0
21094:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21094b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 120(%r31)
	b 21093f
21092:
	rldicl %r8, %r29, 63, 1
21095:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21095b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 120(%r31)
21093:
	li %r5, 29
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 27
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 15
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 120(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21096f
	addi %r8, %r29, 0
21098:
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
	bne %cr0, 21098b
	b 21097f
21096:
	rldicl %r8, %r29, 63, 1
21099:
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
	bne %cr0, 21099b
21097:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 49
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21100f
	addi %r8, %r29, 0
21102:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21102b
	b 21101f
21100:
	rldicl %r8, %r29, 63, 1
21103:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21103b
21101:
	li %r5, 37
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 29
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21104f
	addi %r8, %r29, 0
21106:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21106b
	b 21105f
21104:
	rldicl %r8, %r29, 63, 1
21107:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21107b
21105:
	li %r5, 51
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
21108:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21108b
	rldicr %r4, %r29, 5, 58
21109:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21110f
	addi %r8, %r29, 0
21112:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21112b
	b 21111f
21110:
	rldicl %r8, %r29, 63, 1
21113:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21113b
21111:
	li %r5, 51
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21114f
	addi %r8, %r29, 1
21116:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21116b
	b 21115f
21114:
	rldicl %r8, %r29, 63, 1
21117:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21117b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
21115:
	li %r5, 39
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 51
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 37
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21118f
	addi %r8, %r29, 1
	li %r9, 0
21120:
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
	bne %cr0, 21120b
	b 21119f
21118:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
21121:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21121b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
21119:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 51
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 51
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 39
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21122f
	addi %r8, %r29, 1
21124:
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
	bne %cr0, 21124b
	b 21123f
21122:
	rldicl %r8, %r29, 63, 1
21125:
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
	bne %cr0, 21125b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
21123:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 21109b
	li %r5, 56
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 24
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21126f
	addi %r8, %r29, 0
21128:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21128b
	b 21127f
21126:
	rldicl %r8, %r29, 63, 1
21129:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21129b
21127:
	li %r5, 57
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 25
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21130f
	addi %r8, %r29, 0
21132:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21132b
	b 21131f
21130:
	rldicl %r8, %r29, 63, 1
21133:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21133b
21131:
	li %r5, 55
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21134f
	addi %r8, %r29, 0
21136:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21136b
	b 21135f
21134:
	rldicl %r8, %r29, 63, 1
21137:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21137b
21135:
	rldicr %r11, %r22, 3, 60
21138:
	li %r5, 57
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 124(%r31)
	li %r5, 58
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 56
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 124(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21139f
	addi %r8, %r29, 0
21141:
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
	bne %cr0, 21141b
	b 21140f
21139:
	rldicl %r8, %r29, 63, 1
21142:
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
	bne %cr0, 21142b
21140:
	li %r5, 59
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 58
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21143f
	addi %r8, %r29, 0
	li %r9, 0
21145:
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
	bne %cr0, 21145b
	b 21144f
21143:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
21146:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21146b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
21144:
	li %r5, 55
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 55
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 59
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21147f
	addi %r8, %r29, 0
	li %r9, 0
21149:
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
	bne %cr0, 21149b
	b 21148f
21147:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
21150:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21150b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
21148:
	li %r5, 59
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 10
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 56
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21151f
	addi %r8, %r29, 0
	li %r9, 0
21153:
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
	bne %cr0, 21153b
	b 21152f
21151:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
21154:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21154b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
21152:
	li %r5, 56
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 56
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 59
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21155f
	addi %r8, %r29, 0
	li %r9, 0
21157:
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
	bne %cr0, 21157b
	b 21156f
21155:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
21158:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21158b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
21156:
	li %r9, 0
	li %r5, 57
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21159f
	addi %r8, %r29, 0
21161:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21161b
	b 21160f
21159:
	rldicl %r8, %r29, 63, 1
21162:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21162b
21160:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 21138b
	li %r5, 53
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 55
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21163f
	addi %r8, %r29, 0
21165:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21165b
	b 21164f
21163:
	rldicl %r8, %r29, 63, 1
21166:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21166b
21164:
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 53
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 18
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21167f
	addi %r8, %r29, 0
	li %r9, 0
21169:
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
	bne %cr0, 21169b
	b 21168f
21167:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
21170:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21170b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
21168:
	stw %r9, 120(%r31)
	lwz %r0, 120(%r31)
	li %r3, 1
	xor %r0, %r0, %r3
	lwz %r3, 148(%r31)
	and %r0, %r0, %r3
	stw %r0, 156(%r31)
	lwz %r0, 156(%r31)
	lwz %r3, 116(%r31)
	and %r0, %r0, %r3
	stw %r0, 156(%r31)
	lwz %r0, 156(%r31)
	lwz %r3, 112(%r31)
	and %r0, %r0, %r3
	stw %r0, 156(%r31)
	li %r5, 25
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 120(%r31)
	lwz %r0, 156(%r31)
	lwz %r3, 120(%r31)
	and %r0, %r0, %r3
	stw %r0, 156(%r31)
	lwz %r0, 156(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 156(%r31)
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 20
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 21171f
	addi %r8, %r29, 0
	li %r9, 0
21173:
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
	bne %cr0, 21173b
	b 21172f
21171:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
21174:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21174b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
21172:
	stw %r9, 120(%r31)
	lwz %r0, 144(%r31)
	li %r3, 1
	xor %r0, %r0, %r3
	lwz %r3, 120(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	lwz %r0, 156(%r31)
	lwz %r3, 140(%r31)
	and %r0, %r0, %r3
	stw %r0, 156(%r31)
	lwz %r0, 152(%r31)
	li %r3, 1
	xor %r0, %r0, %r3
	lwz %r3, 156(%r31)
	and %r0, %r0, %r3
	stw %r0, 156(%r31)
	addi %r5, %r14, 0
	addi %r8, %r24, 0
	lwz %r9, 156(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 53
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
21175:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21175b
	addi %r5, %r15, 0
	addi %r8, %r24, 0
	lwz %r9, 156(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 49
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
21176:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21176b
	addi %r5, %r16, 0
	addi %r8, %r22, 0
	lwz %r9, 156(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 24
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
21177:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21177b
	addi %r5, %r17, 0
	addi %r8, %r22, 0
	lwz %r9, 156(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 25
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
21178:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21178b
	addi %r5, %r18, 0
	addi %r8, %r22, 0
	lwz %r9, 156(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 50
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
21179:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21179b
	addi %r5, %r19, 0
	addi %r8, %r22, 0
	lwz %r9, 156(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 51
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
21180:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21180b
	addi %r5, %r20, 0
	addi %r8, %r22, 0
	lwz %r9, 156(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 52
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
21181:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 21181b
	lwz %r3, 152(%r31)
	rldicr %r3, %r3, 1, 62
	lwz %r0, 156(%r31)
	add %r3, %r3, %r0
	ld %r14, 0(%r31)
	ld %r15, 8(%r31)
	ld %r16, 16(%r31)
	ld %r17, 24(%r31)
	ld %r18, 32(%r31)
	ld %r19, 40(%r31)
	ld %r20, 48(%r31)
	ld %r21, 56(%r31)
	ld %r22, 64(%r31)
	ld %r23, 72(%r31)
	ld %r24, 80(%r31)
	ld %r29, 88(%r31)
	ld %r30, 96(%r31)
	ld %r31, 104(%r31)
	blr

vg_rsa_keygen_candidate:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	stdu %r1, -176(%r1)
	addi %r11, %r1, 0
	std %r14, 32(%r11)
	std %r15, 40(%r11)
	std %r16, 48(%r11)
	std %r17, 56(%r11)
	std %r18, 64(%r11)
	std %r19, 72(%r11)
	std %r20, 80(%r11)
	std %r21, 88(%r11)
	std %r22, 96(%r11)
	std %r23, 104(%r11)
	std %r24, 112(%r11)
	std %r25, 120(%r11)
	std %r26, 128(%r11)
	std %r27, 136(%r11)
	std %r28, 144(%r11)
	std %r29, 152(%r11)
	std %r30, 160(%r11)
	std %r31, 168(%r11)
	addi %r23, %r3, 0
	addi %r24, %r4, 0
	addi %r25, %r5, 0
	addi %r21, %r6, 0
	addi %r30, %r7, 0
	addi %r18, %r8, 0
	addi %r19, %r9, 0
	addi %r26, %r10, 0
	addi %r27, %r1, 320
	ld %r27, 0(%r27)
	addi %r31, %r1, 328
	ld %r31, 0(%r31)
	addi %r11, %r1, 336
	ld %r11, 0(%r11)
	li %r28, 0
	addi %r14, %r23, 0
	addi %r17, %r24, 0
	li %r0, 0
20:
	stb %r0, 0(%r14)
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
	subf %r5, %r24, %r27
	rldicl %r5, %r5, 1, 63
	li %r0, 1
	xor %r5, %r5, %r0
	rldicl %r0, %r27, 1, 63
	or %r5, %r5, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 21f
	std %r11, 0(%r31)
	rldicl %r3, %r24, 61, 3
	std %r3, 48(%r31)
	addi %r29, %r3, 2
	rldicr %r29, %r29, 3, 60
	std %r29, 224(%r31)
	addi %r10, %r31, 256
	rldicr %r11, %r3, 1, 62
	addi %r3, %r10, 0
	std %r3, 64(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	std %r3, 72(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	std %r3, 80(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	std %r3, 88(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	std %r3, 96(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	std %r3, 104(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	std %r3, 112(%r31)
	addi %r3, %r10, 0
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	add %r3, %r3, %r29
	std %r3, 120(%r31)
	addi %r14, %r10, 0
	li %r17, 35
	mulld %r17, %r17, %r29
	rldicl %r17, %r17, 61, 3
	li %r0, 0
23:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 23b
	addi %r12, %r26, 0
	addi %r6, %r24, 0
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
	ld %r3, 0(%r10)
	li %r4, 1
	or %r3, %r3, %r4
	std %r3, 0(%r10)
	rldicr %r5, %r11, 2, 61
	add %r5, %r5, %r10
	addi %r5, %r5, -8
	ld %r3, 0(%r5)
	lis %r4, -16384
	rldicr %r4, %r4, 32, 31
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	addi %r28, %r24, 0
	cmpldi %cr0, %r19, 0
	beq %cr0, 26f
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r12, %r18, 0
	addi %r6, %r24, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
28:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 28b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
29:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 29b
	addi %r10, %r31, 256
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
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
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
210:
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
	bne %cr0, 210b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r31, 256
	addi %r22, %r20, 0
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
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r10, %r10, 0
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
211:
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
	bne %cr0, 211b
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
	add %r5, %r5, %r29
	addi %r20, %r22, 0
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
212:
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
	bne %cr0, 212b
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
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	addi %r5, %r5, -16
	lis %r0, 4096
	std %r0, 0(%r5)
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
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
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
213:
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
	bne %cr0, 213b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r31, 256
	li %r0, 1
	and %r22, %r20, %r0
	xor %r22, %r22, %r0
	b 27f
26:
	li %r22, 0
27:
	cmpldi %cr0, %r22, 0
	bne %cr0, 214f
	li %r3, 0
	addi %r14, %r21, 0
	addi %r17, %r30, 0
216:
	rldicr %r3, %r3, 8, 55
	lbz %r0, 0(%r14)
	add %r3, %r3, %r0
	addi %r14, %r14, 1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 216b
	addi %r21, %r3, 0
	li %r0, 1
	and %r5, %r21, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 217f
	addi %r5, %r21, -1
	cmpldi %cr0, %r5, 0
	beq %cr0, 219f
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
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	rldicl %r17, %r11, 63, 1
221:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 221b
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
	rldicr %r5, %r11, 2, 61
	add %r14, %r14, %r5
	rldicl %r17, %r11, 63, 1
	li %r3, 0
222:
	addi %r14, %r14, -8
	ld %r7, 0(%r14)
	li %r6, 64
223:
	rldicl %r8, %r3, 1, 63
	rldicl %r9, %r7, 1, 63
	rldicr %r3, %r3, 1, 62
	add %r3, %r3, %r9
	rldicr %r7, %r7, 1, 62
	rldicr %r15, %r3, 1, 62
	rldicl %r15, %r15, 63, 1
	rldicr %r16, %r21, 1, 62
	rldicl %r16, %r16, 63, 1
	subf %r15, %r16, %r15
	rldicl %r15, %r15, 1, 63
	rldicl %r9, %r3, 1, 63
	rldicl %r16, %r21, 1, 63
	xor %r9, %r9, %r16
	and %r16, %r16, %r9
	li %r0, 1
	xor %r9, %r9, %r0
	and %r9, %r9, %r15
	or %r9, %r9, %r16
	li %r0, 1
	xor %r9, %r9, %r0
	or %r9, %r9, %r8
	li %r0, 0
	subf %r9, %r9, %r0
	subf %r4, %r21, %r3
	xor %r4, %r4, %r3
	and %r4, %r4, %r9
	xor %r3, %r3, %r4
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 223b
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 222b
	li %r9, 128
224:
	rldicr %r15, %r3, 1, 62
	rldicl %r15, %r15, 63, 1
	rldicr %r16, %r21, 1, 62
	rldicl %r16, %r16, 63, 1
	subf %r15, %r16, %r15
	rldicl %r15, %r15, 1, 63
	rldicl %r5, %r3, 1, 63
	rldicl %r16, %r21, 1, 63
	xor %r5, %r5, %r16
	and %r16, %r16, %r5
	li %r0, 1
	xor %r5, %r5, %r0
	and %r5, %r5, %r15
	or %r5, %r5, %r16
	li %r0, 0
	subf %r5, %r5, %r0
	li %r0, 1
	and %r4, %r3, %r0
	li %r0, 0
	subf %r4, %r4, %r0
	subf %r6, %r21, %r3
	subf %r7, %r3, %r21
	xor %r7, %r7, %r6
	and %r7, %r7, %r5
	xor %r6, %r6, %r7
	xor %r7, %r3, %r21
	and %r7, %r7, %r5
	xor %r7, %r7, %r21
	xor %r6, %r6, %r3
	and %r6, %r6, %r4
	xor %r3, %r3, %r6
	xor %r7, %r7, %r21
	and %r7, %r7, %r4
	xor %r21, %r21, %r7
	rldicl %r3, %r3, 63, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 224b
	addi %r22, %r21, -1
	b 220f
219:
	li %r22, 0
220:
	b 218f
217:
	li %r22, 1
218:
	cmpldi %cr0, %r22, 0
	bne %cr0, 225f
	std %r26, 136(%r31)
	std %r27, 144(%r31)
	std %r28, 152(%r31)
	std %r24, 216(%r31)
	ld %r3, 48(%r31)
	li %r5, 27
	addi %r4, %r3, -5
	rldicl %r4, %r4, 1, 63
	addi %r4, %r4, -1
	li %r6, 8
	xor %r6, %r6, %r5
	and %r6, %r6, %r4
	xor %r5, %r5, %r6
	addi %r4, %r3, -6
	rldicl %r4, %r4, 1, 63
	addi %r4, %r4, -1
	li %r6, 7
	xor %r6, %r6, %r5
	and %r6, %r6, %r4
	xor %r5, %r5, %r6
	addi %r4, %r3, -7
	rldicl %r4, %r4, 1, 63
	addi %r4, %r4, -1
	li %r6, 6
	xor %r6, %r6, %r5
	and %r6, %r6, %r4
	xor %r5, %r5, %r6
	addi %r4, %r3, -8
	rldicl %r4, %r4, 1, 63
	addi %r4, %r4, -1
	li %r6, 5
	xor %r6, %r6, %r5
	and %r6, %r6, %r4
	xor %r5, %r5, %r6
	addi %r4, %r3, -22
	rldicl %r4, %r4, 1, 63
	addi %r4, %r4, -1
	li %r6, 4
	xor %r6, %r6, %r5
	and %r6, %r6, %r4
	xor %r5, %r5, %r6
	addi %r4, %r3, -59
	rldicl %r4, %r4, 1, 63
	addi %r4, %r4, -1
	li %r6, 3
	xor %r6, %r6, %r5
	and %r6, %r6, %r4
	xor %r5, %r5, %r6
	std %r5, 168(%r31)
	li %r4, 16
	subf %r4, %r3, %r4
	rldicl %r4, %r4, 1, 63
	li %r5, 512
	mulld %r4, %r4, %r5
	add %r4, %r4, %r5
	std %r4, 128(%r31)
	std %r23, 24(%r31)
	std %r24, 40(%r31)
	bcl 20, 31, 2f
2:
	mflr %r23
	addis %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	addi %r23, %r23, ({VG_RSA_KEYGEN_TRIAL32}
	ld %r24, 128(%r31)
227:
	ld %r8, 0(%r23)
	rldicl %r9, %r8, 32, 32
	rldicr %r8, %r8, 32, 31
	rldicl %r8, %r8, 32, 32
	li %r3, 0
	addi %r5, %r10, 0
	addi %r4, %r11, 0
228:
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
	bne %cr0, 228b
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
	bne %cr0, 227b
	ld %r23, 24(%r31)
	ld %r24, 40(%r31)
	cmpldi %cr0, %r22, 0
	bne %cr0, 229f
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
231:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 231b
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	addi %r14, %r14, -8
	li %r0, 1
	std %r0, 0(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r4, %r4, 64
232:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
233:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 233b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
234:
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
	bne %cr0, 234b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
235:
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
	bne %cr0, 235b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 232b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
246:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 246b
247:
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
	beq %cr0, 248f
250:
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
	bne %cr0, 250b
	b 249f
248:
249:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 251f
253:
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
	bne %cr0, 253b
	b 252f
251:
252:
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
	bne %cr0, 247b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
254:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 254b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
255:
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
	bne %cr0, 255b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
256:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 256b
257:
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
	beq %cr0, 258f
260:
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
	bne %cr0, 260b
	b 259f
258:
259:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 261f
263:
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
	bne %cr0, 263b
	b 262f
261:
262:
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
	bne %cr0, 257b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
266:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 266b
267:
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
	beq %cr0, 268f
270:
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
	bne %cr0, 270b
	b 269f
268:
269:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 271f
273:
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
	bne %cr0, 273b
	b 272f
271:
272:
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
	bne %cr0, 267b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
274:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 274b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
275:
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
	bne %cr0, 275b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
276:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 276b
277:
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
	beq %cr0, 278f
280:
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
	bne %cr0, 280b
	b 279f
278:
279:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 281f
283:
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
	bne %cr0, 283b
	b 282f
281:
282:
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
	bne %cr0, 277b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
286:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 286b
287:
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
	beq %cr0, 288f
290:
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
	bne %cr0, 290b
	b 289f
288:
289:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
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
	bne %cr0, 293b
	b 292f
291:
292:
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
	bne %cr0, 287b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
294:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 294b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
295:
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
	bne %cr0, 295b
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
296:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 296b
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
297:
	std %r22, 0(%r14)
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
	beq %cr0, 299f
2101:
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
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 298b
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
2107:
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
	bne %cr0, 2107b
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
2108:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2108b
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r6, 0
	li %r4, 1
2109:
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
	bne %cr0, 2109b
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
2110:
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
	bne %cr0, 2110b
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
2111:
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
	bne %cr0, 2111b
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
2112:
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
	bne %cr0, 2112b
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
2113:
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
	bne %cr0, 2113b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	li %r3, 1
	std %r3, 176(%r31)
	li %r3, 0
	std %r3, 16(%r31)
	li %r3, 4
	std %r3, 160(%r31)
2114:
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
	beq %cr0, 2115f
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
2117:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2117b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2118:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2118b
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r21, 0(%r5)
	rldicl %r21, %r21, 63, 1
	addi %r5, %r5, 8
	rldicl %r6, %r11, 63, 1
	addi %r6, %r6, -1
2119:
	ld %r3, 0(%r5)
	or %r21, %r21, %r3
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2119b
	rldicl %r3, %r21, 63, 1
	li %r0, 1
	and %r21, %r21, %r0
	or %r21, %r21, %r3
	addi %r21, %r21, -1
	rldicl %r21, %r21, 1, 63
	xor %r21, %r21, %r0
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
2120:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2120b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	li %r0, 0
	std %r0, 0(%r5)
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r3, 0(%r5)
	li %r4, 1
	or %r3, %r3, %r4
	std %r3, 0(%r5)
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
2121:
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
	bne %cr0, 2121b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	li %r0, 1
	and %r3, %r20, %r0
	and %r21, %r21, %r3
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
2122:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2122b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	li %r0, 0
	std %r0, 0(%r5)
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r3, 0(%r5)
	li %r4, 2
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	addi %r5, %r5, -8
	li %r4, 0
	addi %r4, %r4, -1
	rldicl %r4, %r4, 63, 1
	ld %r3, 0(%r5)
	and %r3, %r3, %r4
	std %r3, 0(%r5)
	li %r0, 0
	subf %r20, %r21, %r0
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	add %r8, %r8, %r29
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
	add %r5, %r5, %r29
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
	li %r20, 0
	addi %r20, %r20, -1
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
	addi %r5, %r10, 0
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
	ld %r3, 16(%r31)
	add %r3, %r3, %r21
	std %r3, 16(%r31)
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
2125:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2125b
2126:
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
	beq %cr0, 2127f
2129:
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
	bne %cr0, 2129b
	b 2128f
2127:
2128:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2130f
2132:
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
	bne %cr0, 2132b
	b 2131f
2130:
2131:
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
	bne %cr0, 2126b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2133:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2133b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
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
	beq %cr0, 2135f
	ld %r3, 176(%r31)
	addi %r3, %r3, 1
	std %r3, 176(%r31)
	li %r4, 17
	subf %r5, %r4, %r3
	rldicl %r5, %r5, 1, 63
	li %r0, 1
	xor %r5, %r5, %r0
	rldicl %r0, %r3, 1, 63
	or %r5, %r5, %r0
	addi %r7, %r5, 0
	ld %r3, 16(%r31)
	ld %r4, 168(%r31)
	subf %r5, %r4, %r3
	rldicl %r5, %r5, 1, 63
	li %r0, 1
	xor %r5, %r5, %r0
	rldicl %r0, %r3, 1, 63
	or %r5, %r5, %r0
	and %r5, %r5, %r7
	li %r4, 3
	mulld %r5, %r5, %r4
	li %r4, 4
	subf %r5, %r5, %r4
	std %r5, 160(%r31)
	b 2136f
2135:
	li %r3, 2
	std %r3, 160(%r31)
2136:
	b 2116f
2115:
	li %r3, 0
	std %r3, 160(%r31)
2116:
	ld %r3, 160(%r31)
	addi %r3, %r3, -4
	cmpldi %cr0, %r3, 0
	beq %cr0, 2114b
	ld %r28, 152(%r31)
	ld %r3, 160(%r31)
	cmpldi %cr0, %r3, 0
	beq %cr0, 2137f
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 2139f
	std %r28, 0(%r25)
	li %r3, 3
	b 2140f
2139:
	addi %r10, %r31, 256
	add %r15, %r10, %r24
	addi %r15, %r15, -1
	addi %r16, %r23, 0
	addi %r17, %r24, 0
2141:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2141b
	std %r28, 0(%r25)
	li %r3, 1
2140:
	b 2138f
2137:
	li %r28, 0
	std %r28, 0(%r25)
	li %r3, 0
2138:
	b 230f
229:
	std %r28, 0(%r25)
	li %r3, 3
230:
	b 226f
225:
	std %r28, 0(%r25)
	li %r3, 3
226:
	b 215f
214:
	std %r28, 0(%r25)
	li %r3, 2
215:
	b 22f
21:
	li %r28, 0
	std %r28, 0(%r25)
	li %r3, 0
22:
	addi %r11, %r1, 0
	ld %r14, 32(%r11)
	ld %r15, 40(%r11)
	ld %r16, 48(%r11)
	ld %r17, 56(%r11)
	ld %r18, 64(%r11)
	ld %r19, 72(%r11)
	ld %r20, 80(%r11)
	ld %r21, 88(%r11)
	ld %r22, 96(%r11)
	ld %r23, 104(%r11)
	ld %r24, 112(%r11)
	ld %r25, 120(%r11)
	ld %r26, 128(%r11)
	ld %r27, 136(%r11)
	ld %r28, 144(%r11)
	ld %r29, 152(%r11)
	ld %r30, 160(%r11)
	ld %r31, 168(%r11)
	addi %r1, %r1, 176
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
