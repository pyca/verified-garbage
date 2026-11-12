// The functions of `src/internal/vg_rsa_keygen_key.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
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
	rldicl %r11, %r22, 62, 2
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	addi %r10, %r11, 0
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
2146:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2146b
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	li %r0, 0
	std %r0, 0(%r6)
	li %r4, 2
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	ld %r5, 0(%r4)
	addi %r6, %r5, 0
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	li %r3, 0
	subf %r12, %r6, %r3
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	std %r12, 40(%r4)
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2147:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2147b
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r11, 0(%r5)
	li %r0, 1
	and %r11, %r11, %r0
	xor %r11, %r11, %r0
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	li %r9, 0
2148:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2148b
	std %r9, 0(%r5)
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r0, 0
2149:
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2149b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r0, 0
2150:
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2150b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	std %r0, 0(%r5)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	std %r0, 0(%r5)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	add %r3, %r8, %r8
	add %r3, %r3, %r8
	addi %r3, %r3, 2
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
2151:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r4, 0(%r5)
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r5, 0(%r5)
	li %r3, 14
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r3, 0(%r3)
	li %r6, 1
	li %r7, 0
	li %r8, 0
	li %r9, 1
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	std %r3, 0(%r4)
	std %r6, 8(%r4)
	std %r7, 16(%r4)
	std %r8, 24(%r4)
	std %r9, 32(%r4)
	li %r3, 11
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r14, 0(%r3)
	std %r15, 8(%r3)
	std %r16, 16(%r3)
	std %r17, 24(%r3)
	std %r18, 32(%r3)
	std %r19, 40(%r3)
	li %r3, 12
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r20, 0(%r3)
	std %r21, 8(%r3)
	std %r22, 16(%r3)
	std %r23, 24(%r3)
	std %r24, 32(%r3)
	std %r25, 40(%r3)
	li %r3, 13
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r26, 0(%r3)
	std %r27, 8(%r3)
	std %r28, 16(%r3)
	li %r14, 14
	mulld %r14, %r14, %r30
	add %r14, %r14, %r31
	addi %r14, %r14, 160
	ld %r14, 8(%r14)
	li %r15, 14
	mulld %r15, %r15, %r30
	add %r15, %r15, %r31
	addi %r15, %r15, 160
	ld %r15, 16(%r15)
	li %r16, 14
	mulld %r16, %r16, %r30
	add %r16, %r16, %r31
	addi %r16, %r16, 160
	ld %r16, 24(%r16)
	li %r17, 14
	mulld %r17, %r17, %r30
	add %r17, %r17, %r31
	addi %r17, %r17, 160
	ld %r17, 32(%r17)
	li %r0, 0
	rldicl %r18, %r14, 1, 63
	subf %r18, %r18, %r0
	rldicl %r19, %r15, 1, 63
	subf %r19, %r19, %r0
	rldicl %r20, %r16, 1, 63
	subf %r20, %r20, %r0
	rldicl %r21, %r17, 1, 63
	subf %r21, %r21, %r0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r22, 0
	li %r23, 0
	li %r24, 0
	li %r25, 0
	ld %r26, 0(%r5)
	ld %r27, 0(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicl %r28, %r22, 5, 59
	rldicl %r12, %r24, 5, 59
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
2152:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicr %r3, %r22, 5, 58
	add %r3, %r3, %r28
	std %r3, 0(%r5)
	rldicl %r28, %r22, 5, 59
	rldicr %r3, %r24, 5, 58
	add %r3, %r3, %r12
	std %r3, 0(%r6)
	rldicl %r12, %r24, 5, 59
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2152b
	rldicl %r0, %r28, 60, 4
	rldicr %r0, %r0, 5, 58
	subf %r0, %r0, %r28
	std %r0, 0(%r5)
	rldicl %r0, %r12, 60, 4
	rldicr %r0, %r0, 5, 58
	subf %r0, %r0, %r12
	std %r0, 0(%r6)
	li %r14, 14
	mulld %r14, %r14, %r30
	add %r14, %r14, %r31
	addi %r14, %r14, 160
	ld %r14, 8(%r14)
	li %r15, 14
	mulld %r15, %r15, %r30
	add %r15, %r15, %r31
	addi %r15, %r15, 160
	ld %r15, 16(%r15)
	li %r16, 14
	mulld %r16, %r16, %r30
	add %r16, %r16, %r31
	addi %r16, %r16, 160
	ld %r16, 24(%r16)
	li %r17, 14
	mulld %r17, %r17, %r30
	add %r17, %r17, %r31
	addi %r17, %r17, 160
	ld %r17, 32(%r17)
	li %r0, 0
	rldicl %r18, %r14, 1, 63
	subf %r18, %r18, %r0
	rldicl %r19, %r15, 1, 63
	subf %r19, %r19, %r0
	rldicl %r20, %r16, 1, 63
	subf %r20, %r20, %r0
	rldicl %r21, %r17, 1, 63
	subf %r21, %r21, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r22, 0
	li %r23, 0
	li %r24, 0
	li %r25, 0
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	ld %r4, 40(%r4)
	li %r9, 0
	li %r11, 0
	ld %r26, 0(%r5)
	ld %r27, 0(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	mulld %r28, %r22, %r4
	mulld %r12, %r24, %r4
	ld %r4, 0(%r7)
	mulld %r3, %r28, %r4
	addc %r3, %r3, %r22
	mulhdu %r0, %r28, %r4
	addze %r0, %r0
	addc %r22, %r3, %r9
	addze %r9, %r0
	mulld %r3, %r12, %r4
	addc %r3, %r3, %r24
	mulhdu %r0, %r12, %r4
	addze %r0, %r0
	addc %r24, %r3, %r11
	addze %r11, %r0
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	beq %cr0, 2153f
2155:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	ld %r4, 8(%r7)
	mulld %r3, %r28, %r4
	addc %r3, %r3, %r22
	mulhdu %r0, %r28, %r4
	addze %r0, %r0
	addc %r22, %r3, %r9
	addze %r9, %r0
	std %r22, 0(%r5)
	mulld %r3, %r12, %r4
	addc %r3, %r3, %r24
	mulhdu %r0, %r12, %r4
	addze %r0, %r0
	addc %r24, %r3, %r11
	addze %r11, %r0
	std %r24, 0(%r6)
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2155b
	b 2154f
2153:
2154:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicl %r3, %r22, 1, 63
	li %r4, 0
	subf %r3, %r3, %r4
	addc %r22, %r22, %r9
	addze %r3, %r3
	std %r22, 0(%r5)
	std %r3, 8(%r5)
	rldicl %r3, %r24, 1, 63
	subf %r3, %r3, %r4
	addc %r24, %r24, %r11
	addze %r3, %r3
	std %r24, 0(%r6)
	std %r3, 8(%r6)
	li %r3, 11
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r14, 0(%r3)
	ld %r15, 8(%r3)
	ld %r16, 16(%r3)
	ld %r17, 24(%r3)
	ld %r18, 32(%r3)
	ld %r19, 40(%r3)
	li %r3, 12
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r20, 0(%r3)
	ld %r21, 8(%r3)
	ld %r22, 16(%r3)
	ld %r23, 24(%r3)
	ld %r24, 32(%r3)
	ld %r25, 40(%r3)
	li %r3, 13
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r26, 0(%r3)
	ld %r27, 8(%r3)
	ld %r28, 16(%r3)
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 2151b
	li %r11, 1
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r9, 0
2156:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2156b
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2157:
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
	bne %cr0, 2157b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2158:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2158b
	li %r9, 0
	adde %r9, %r9, %r9
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2159:
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
	bne %cr0, 2159b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2160:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2160b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2161:
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
	bne %cr0, 2161b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2162:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2162b
	li %r9, 0
	adde %r9, %r9, %r9
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2163:
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
	bne %cr0, 2163b
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r3, %r8, 4, 59
	subf %r3, %r8, %r3
	addi %r3, %r3, 10
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
2164:
	li %r11, 1
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r9, 0
2165:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2165b
	li %r5, 11
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
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
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
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2167:
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
	bne %cr0, 2167b
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 2164b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 2
	li %r0, 0
2168:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2168b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2169:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2169b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2170:
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
	bne %cr0, 2170b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 2
	li %r0, 0
2171:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2171b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2172:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2172b
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
	beq %cr0, 2173f
	addi %r8, %r29, 0
2175:
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
	bne %cr0, 2175b
	b 2174f
2173:
	rldicl %r8, %r29, 63, 1
2176:
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
	bne %cr0, 2176b
2174:
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
	beq %cr0, 2177f
	addi %r8, %r29, 0
2179:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2179b
	b 2178f
2177:
	rldicl %r8, %r29, 63, 1
2180:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2180b
2178:
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
	beq %cr0, 2181f
	addi %r8, %r29, 0
2183:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2183b
	b 2182f
2181:
	rldicl %r8, %r29, 63, 1
2184:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2184b
2182:
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2185:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2185b
	rldicr %r4, %r29, 5, 58
2186:
	li %r5, 36
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2187f
	addi %r8, %r29, 0
2189:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2189b
	b 2188f
2187:
	rldicl %r8, %r29, 63, 1
2190:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2190b
2188:
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2191f
	addi %r8, %r29, 1
2193:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2193b
	b 2192f
2191:
	rldicl %r8, %r29, 63, 1
2194:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2194b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2192:
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
	beq %cr0, 2195f
	addi %r8, %r29, 1
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
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2196:
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
	beq %cr0, 2199f
	addi %r8, %r29, 1
2201:
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
	bne %cr0, 2201b
	b 2200f
2199:
	rldicl %r8, %r29, 63, 1
2202:
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
	bne %cr0, 2202b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2200:
	li %r5, 36
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2186b
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
	beq %cr0, 2203f
	addi %r8, %r29, 0
2205:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2205b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 140(%r31)
	b 2204f
2203:
	rldicl %r8, %r29, 63, 1
2206:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2206b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 140(%r31)
2204:
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
	beq %cr0, 2215f
	addi %r8, %r29, 0
2217:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2217b
	b 2216f
2215:
	rldicl %r8, %r29, 63, 1
2218:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2218b
2216:
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
	beq %cr0, 2219f
	addi %r8, %r29, 0
2221:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2221b
	b 2220f
2219:
	rldicl %r8, %r29, 63, 1
2222:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2222b
2220:
	li %r5, 42
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2223:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2223b
	rldicr %r4, %r29, 5, 58
2224:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2225f
	addi %r8, %r29, 0
2227:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2227b
	b 2226f
2225:
	rldicl %r8, %r29, 63, 1
2228:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2228b
2226:
	li %r5, 42
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2229f
	addi %r8, %r29, 1
2231:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2231b
	b 2230f
2229:
	rldicl %r8, %r29, 63, 1
2232:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2232b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2230:
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
	beq %cr0, 2233f
	addi %r8, %r29, 1
	li %r9, 0
2235:
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
	bne %cr0, 2235b
	b 2234f
2233:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2236:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2236b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2234:
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
	beq %cr0, 2237f
	addi %r8, %r29, 1
2239:
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
	bne %cr0, 2239b
	b 2238f
2237:
	rldicl %r8, %r29, 63, 1
2240:
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
	bne %cr0, 2240b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2238:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2224b
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
	beq %cr0, 2241f
	addi %r8, %r29, 0
2243:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2243b
	b 2242f
2241:
	rldicl %r8, %r29, 63, 1
2244:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2244b
2242:
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
	beq %cr0, 2245f
	addi %r8, %r29, 0
2247:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2247b
	b 2246f
2245:
	rldicl %r8, %r29, 63, 1
2248:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2248b
2246:
	li %r11, 2
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	addi %r10, %r11, 0
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
2249:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2249b
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	li %r0, 0
	std %r0, 0(%r6)
	li %r4, 2
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	ld %r5, 0(%r4)
	addi %r6, %r5, 0
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	li %r3, 0
	subf %r12, %r6, %r3
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	std %r12, 40(%r4)
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2250:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2250b
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r11, 0(%r5)
	li %r0, 1
	and %r11, %r11, %r0
	xor %r11, %r11, %r0
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	li %r9, 0
2251:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2251b
	std %r9, 0(%r5)
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r0, 0
2252:
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2252b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r0, 0
2253:
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2253b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	std %r0, 0(%r5)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	std %r0, 0(%r5)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	add %r3, %r8, %r8
	add %r3, %r3, %r8
	addi %r3, %r3, 2
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
2254:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r4, 0(%r5)
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r5, 0(%r5)
	li %r3, 14
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r3, 0(%r3)
	li %r6, 1
	li %r7, 0
	li %r8, 0
	li %r9, 1
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	std %r3, 0(%r4)
	std %r6, 8(%r4)
	std %r7, 16(%r4)
	std %r8, 24(%r4)
	std %r9, 32(%r4)
	li %r3, 11
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r14, 0(%r3)
	std %r15, 8(%r3)
	std %r16, 16(%r3)
	std %r17, 24(%r3)
	std %r18, 32(%r3)
	std %r19, 40(%r3)
	li %r3, 12
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r20, 0(%r3)
	std %r21, 8(%r3)
	std %r22, 16(%r3)
	std %r23, 24(%r3)
	std %r24, 32(%r3)
	std %r25, 40(%r3)
	li %r3, 13
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r26, 0(%r3)
	std %r27, 8(%r3)
	std %r28, 16(%r3)
	li %r14, 14
	mulld %r14, %r14, %r30
	add %r14, %r14, %r31
	addi %r14, %r14, 160
	ld %r14, 8(%r14)
	li %r15, 14
	mulld %r15, %r15, %r30
	add %r15, %r15, %r31
	addi %r15, %r15, 160
	ld %r15, 16(%r15)
	li %r16, 14
	mulld %r16, %r16, %r30
	add %r16, %r16, %r31
	addi %r16, %r16, 160
	ld %r16, 24(%r16)
	li %r17, 14
	mulld %r17, %r17, %r30
	add %r17, %r17, %r31
	addi %r17, %r17, 160
	ld %r17, 32(%r17)
	li %r0, 0
	rldicl %r18, %r14, 1, 63
	subf %r18, %r18, %r0
	rldicl %r19, %r15, 1, 63
	subf %r19, %r19, %r0
	rldicl %r20, %r16, 1, 63
	subf %r20, %r20, %r0
	rldicl %r21, %r17, 1, 63
	subf %r21, %r21, %r0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r22, 0
	li %r23, 0
	li %r24, 0
	li %r25, 0
	ld %r26, 0(%r5)
	ld %r27, 0(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicl %r28, %r22, 5, 59
	rldicl %r12, %r24, 5, 59
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
2255:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicr %r3, %r22, 5, 58
	add %r3, %r3, %r28
	std %r3, 0(%r5)
	rldicl %r28, %r22, 5, 59
	rldicr %r3, %r24, 5, 58
	add %r3, %r3, %r12
	std %r3, 0(%r6)
	rldicl %r12, %r24, 5, 59
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2255b
	rldicl %r0, %r28, 60, 4
	rldicr %r0, %r0, 5, 58
	subf %r0, %r0, %r28
	std %r0, 0(%r5)
	rldicl %r0, %r12, 60, 4
	rldicr %r0, %r0, 5, 58
	subf %r0, %r0, %r12
	std %r0, 0(%r6)
	li %r14, 14
	mulld %r14, %r14, %r30
	add %r14, %r14, %r31
	addi %r14, %r14, 160
	ld %r14, 8(%r14)
	li %r15, 14
	mulld %r15, %r15, %r30
	add %r15, %r15, %r31
	addi %r15, %r15, 160
	ld %r15, 16(%r15)
	li %r16, 14
	mulld %r16, %r16, %r30
	add %r16, %r16, %r31
	addi %r16, %r16, 160
	ld %r16, 24(%r16)
	li %r17, 14
	mulld %r17, %r17, %r30
	add %r17, %r17, %r31
	addi %r17, %r17, 160
	ld %r17, 32(%r17)
	li %r0, 0
	rldicl %r18, %r14, 1, 63
	subf %r18, %r18, %r0
	rldicl %r19, %r15, 1, 63
	subf %r19, %r19, %r0
	rldicl %r20, %r16, 1, 63
	subf %r20, %r20, %r0
	rldicl %r21, %r17, 1, 63
	subf %r21, %r21, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r22, 0
	li %r23, 0
	li %r24, 0
	li %r25, 0
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	ld %r4, 40(%r4)
	li %r9, 0
	li %r11, 0
	ld %r26, 0(%r5)
	ld %r27, 0(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	mulld %r28, %r22, %r4
	mulld %r12, %r24, %r4
	ld %r4, 0(%r7)
	mulld %r3, %r28, %r4
	addc %r3, %r3, %r22
	mulhdu %r0, %r28, %r4
	addze %r0, %r0
	addc %r22, %r3, %r9
	addze %r9, %r0
	mulld %r3, %r12, %r4
	addc %r3, %r3, %r24
	mulhdu %r0, %r12, %r4
	addze %r0, %r0
	addc %r24, %r3, %r11
	addze %r11, %r0
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	beq %cr0, 2256f
2258:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	ld %r4, 8(%r7)
	mulld %r3, %r28, %r4
	addc %r3, %r3, %r22
	mulhdu %r0, %r28, %r4
	addze %r0, %r0
	addc %r22, %r3, %r9
	addze %r9, %r0
	std %r22, 0(%r5)
	mulld %r3, %r12, %r4
	addc %r3, %r3, %r24
	mulhdu %r0, %r12, %r4
	addze %r0, %r0
	addc %r24, %r3, %r11
	addze %r11, %r0
	std %r24, 0(%r6)
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2258b
	b 2257f
2256:
2257:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicl %r3, %r22, 1, 63
	li %r4, 0
	subf %r3, %r3, %r4
	addc %r22, %r22, %r9
	addze %r3, %r3
	std %r22, 0(%r5)
	std %r3, 8(%r5)
	rldicl %r3, %r24, 1, 63
	subf %r3, %r3, %r4
	addc %r24, %r24, %r11
	addze %r3, %r3
	std %r24, 0(%r6)
	std %r3, 8(%r6)
	li %r3, 11
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r14, 0(%r3)
	ld %r15, 8(%r3)
	ld %r16, 16(%r3)
	ld %r17, 24(%r3)
	ld %r18, 32(%r3)
	ld %r19, 40(%r3)
	li %r3, 12
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r20, 0(%r3)
	ld %r21, 8(%r3)
	ld %r22, 16(%r3)
	ld %r23, 24(%r3)
	ld %r24, 32(%r3)
	ld %r25, 40(%r3)
	li %r3, 13
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r26, 0(%r3)
	ld %r27, 8(%r3)
	ld %r28, 16(%r3)
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 2254b
	li %r11, 1
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r9, 0
2259:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2259b
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2260:
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
	bne %cr0, 2260b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2261:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2261b
	li %r9, 0
	adde %r9, %r9, %r9
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2262:
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
	bne %cr0, 2262b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2263:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2263b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2264:
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
	bne %cr0, 2264b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2265:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2265b
	li %r9, 0
	adde %r9, %r9, %r9
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
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
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r3, %r8, 4, 59
	subf %r3, %r8, %r3
	addi %r3, %r3, 10
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
2267:
	li %r11, 1
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r9, 0
2268:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2268b
	li %r5, 11
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
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2269:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2269b
	li %r9, 0
	adde %r9, %r9, %r9
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2270:
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
	bne %cr0, 2270b
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 2267b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 2
	li %r0, 0
2271:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2271b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2272:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2272b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2273:
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
	bne %cr0, 2273b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 2
	li %r0, 0
2274:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2274b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2275:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2275b
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
	beq %cr0, 2276f
	addi %r8, %r29, 0
2278:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2278b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 116(%r31)
	b 2277f
2276:
	rldicl %r8, %r29, 63, 1
2279:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2279b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 116(%r31)
2277:
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
	beq %cr0, 2280f
	addi %r8, %r29, 0
	li %r9, 0
2282:
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
	bne %cr0, 2282b
	b 2281f
2280:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2283:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2283b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2281:
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
	beq %cr0, 2284f
	addi %r8, %r29, 0
2286:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2286b
	b 2285f
2284:
	rldicl %r8, %r29, 63, 1
2287:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2287b
2285:
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
	beq %cr0, 2288f
	addi %r8, %r29, 0
2290:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2290b
	b 2289f
2288:
	rldicl %r8, %r29, 63, 1
2291:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2291b
2289:
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
	beq %cr0, 2292f
	addi %r8, %r29, 0
2294:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2294b
	b 2293f
2292:
	rldicl %r8, %r29, 63, 1
2295:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2295b
2293:
	li %r11, 64
2296:
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
	beq %cr0, 2297f
	addi %r8, %r29, 0
2299:
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
	bne %cr0, 2299b
	b 2298f
2297:
	rldicl %r8, %r29, 63, 1
2300:
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
	bne %cr0, 2300b
2298:
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
	beq %cr0, 2301f
	addi %r8, %r29, 0
	li %r9, 0
2303:
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
	bne %cr0, 2303b
	b 2302f
2301:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2304:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2304b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2302:
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
	beq %cr0, 2305f
	addi %r8, %r29, 0
	li %r9, 0
2307:
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
	bne %cr0, 2307b
	b 2306f
2305:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2308:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2308b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2306:
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
	beq %cr0, 2309f
	addi %r8, %r29, 0
	li %r9, 0
2311:
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
	bne %cr0, 2311b
	b 2310f
2309:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2312:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2312b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2310:
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
	beq %cr0, 2313f
	addi %r8, %r29, 0
	li %r9, 0
2315:
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
	bne %cr0, 2315b
	b 2314f
2313:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2316:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2316b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2314:
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
	beq %cr0, 2317f
	addi %r8, %r29, 0
2319:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2319b
	b 2318f
2317:
	rldicl %r8, %r29, 63, 1
2320:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2320b
2318:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 2296b
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
	beq %cr0, 2321f
	addi %r8, %r29, 0
2323:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2323b
	b 2322f
2321:
	rldicl %r8, %r29, 63, 1
2324:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2324b
2322:
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
	beq %cr0, 2325f
	addi %r8, %r29, 0
2327:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2327b
	b 2326f
2325:
	rldicl %r8, %r29, 63, 1
2328:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2328b
2326:
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
	beq %cr0, 2329f
	addi %r8, %r29, 0
2331:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2331b
	b 2330f
2329:
	rldicl %r8, %r29, 63, 1
2332:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2332b
2330:
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
	beq %cr0, 2333f
	addi %r8, %r29, 0
2335:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2335b
	b 2334f
2333:
	rldicl %r8, %r29, 63, 1
2336:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2336b
2334:
	li %r11, 64
2337:
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
	beq %cr0, 2338f
	addi %r8, %r29, 0
2340:
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
	bne %cr0, 2340b
	b 2339f
2338:
	rldicl %r8, %r29, 63, 1
2341:
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
	bne %cr0, 2341b
2339:
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
	beq %cr0, 2342f
	addi %r8, %r29, 0
	li %r9, 0
2344:
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
	bne %cr0, 2344b
	b 2343f
2342:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2345:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2345b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2343:
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
	beq %cr0, 2346f
	addi %r8, %r29, 0
	li %r9, 0
2348:
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
	bne %cr0, 2348b
	b 2347f
2346:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2349:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2349b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2347:
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
	beq %cr0, 2350f
	addi %r8, %r29, 0
	li %r9, 0
2352:
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
	bne %cr0, 2352b
	b 2351f
2350:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2353:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2353b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2351:
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
	beq %cr0, 2354f
	addi %r8, %r29, 0
	li %r9, 0
2356:
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
	bne %cr0, 2356b
	b 2355f
2354:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2357:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2357b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2355:
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
	beq %cr0, 2358f
	addi %r8, %r29, 0
2360:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2360b
	b 2359f
2358:
	rldicl %r8, %r29, 63, 1
2361:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2361b
2359:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 2337b
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
	beq %cr0, 2362f
	addi %r8, %r29, 0
2364:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2364b
	b 2363f
2362:
	rldicl %r8, %r29, 63, 1
2365:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2365b
2363:
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
	beq %cr0, 2366f
	addi %r8, %r29, 0
	li %r9, 0
2368:
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
	bne %cr0, 2368b
	b 2367f
2366:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2369:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2369b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2367:
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
	beq %cr0, 2370f
	addi %r8, %r29, 0
	li %r9, 0
2372:
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
	bne %cr0, 2372b
	b 2371f
2370:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2373:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2373b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2371:
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2374:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2374b
	rldicr %r4, %r29, 5, 58
2375:
	li %r5, 45
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2376f
	addi %r8, %r29, 0
2378:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2378b
	b 2377f
2376:
	rldicl %r8, %r29, 63, 1
2379:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2379b
2377:
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2380f
	addi %r8, %r29, 1
2382:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2382b
	b 2381f
2380:
	rldicl %r8, %r29, 63, 1
2383:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2383b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2381:
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
	beq %cr0, 2384f
	addi %r8, %r29, 1
	li %r9, 0
2386:
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
	bne %cr0, 2386b
	b 2385f
2384:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2387:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2387b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2385:
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
	beq %cr0, 2388f
	addi %r8, %r29, 1
2390:
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
	bne %cr0, 2390b
	b 2389f
2388:
	rldicl %r8, %r29, 63, 1
2391:
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
	bne %cr0, 2391b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2389:
	li %r5, 45
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2375b
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
	beq %cr0, 2392f
	addi %r8, %r29, 0
2394:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2394b
	b 2393f
2392:
	rldicl %r8, %r29, 63, 1
2395:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2395b
2393:
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
	beq %cr0, 2396f
	addi %r8, %r29, 0
	li %r9, 0
2398:
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
	bne %cr0, 2398b
	b 2397f
2396:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2399:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2399b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2397:
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
	beq %cr0, 2408f
	addi %r8, %r29, 0
2410:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2410b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 112(%r31)
	b 2409f
2408:
	rldicl %r8, %r29, 63, 1
2411:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2411b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 112(%r31)
2409:
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
	beq %cr0, 2416f
	addi %r8, %r29, 0
	li %r9, 0
2418:
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
	bne %cr0, 2418b
	b 2417f
2416:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2419:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2419b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2417:
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
	beq %cr0, 2420f
	addi %r8, %r29, 0
2422:
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
	bne %cr0, 2422b
	b 2421f
2420:
	rldicl %r8, %r29, 63, 1
2423:
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
	bne %cr0, 2423b
2421:
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
	beq %cr0, 2424f
	addi %r8, %r29, 0
2426:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2426b
	b 2425f
2424:
	rldicl %r8, %r29, 63, 1
2427:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2427b
2425:
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
	beq %cr0, 2428f
	addi %r8, %r29, 0
2430:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2430b
	b 2429f
2428:
	rldicl %r8, %r29, 63, 1
2431:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2431b
2429:
	addi %r11, %r29, 0
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	addi %r10, %r11, 0
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
2432:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2432b
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	li %r0, 0
	std %r0, 0(%r6)
	li %r4, 2
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	ld %r5, 0(%r4)
	addi %r6, %r5, 0
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	li %r3, 0
	subf %r12, %r6, %r3
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	std %r12, 40(%r4)
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2433:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2433b
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r11, 0(%r5)
	li %r0, 1
	and %r11, %r11, %r0
	xor %r11, %r11, %r0
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	li %r9, 0
2434:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2434b
	std %r9, 0(%r5)
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r0, 0
2435:
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2435b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r0, 0
2436:
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2436b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	std %r0, 0(%r5)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	std %r0, 0(%r5)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	add %r3, %r8, %r8
	add %r3, %r3, %r8
	addi %r3, %r3, 2
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
2437:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r4, 0(%r5)
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r5, 0(%r5)
	li %r3, 14
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r3, 0(%r3)
	li %r6, 1
	li %r7, 0
	li %r8, 0
	li %r9, 1
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	std %r3, 0(%r4)
	std %r6, 8(%r4)
	std %r7, 16(%r4)
	std %r8, 24(%r4)
	std %r9, 32(%r4)
	li %r3, 11
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r14, 0(%r3)
	std %r15, 8(%r3)
	std %r16, 16(%r3)
	std %r17, 24(%r3)
	std %r18, 32(%r3)
	std %r19, 40(%r3)
	li %r3, 12
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r20, 0(%r3)
	std %r21, 8(%r3)
	std %r22, 16(%r3)
	std %r23, 24(%r3)
	std %r24, 32(%r3)
	std %r25, 40(%r3)
	li %r3, 13
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r26, 0(%r3)
	std %r27, 8(%r3)
	std %r28, 16(%r3)
	li %r14, 14
	mulld %r14, %r14, %r30
	add %r14, %r14, %r31
	addi %r14, %r14, 160
	ld %r14, 8(%r14)
	li %r15, 14
	mulld %r15, %r15, %r30
	add %r15, %r15, %r31
	addi %r15, %r15, 160
	ld %r15, 16(%r15)
	li %r16, 14
	mulld %r16, %r16, %r30
	add %r16, %r16, %r31
	addi %r16, %r16, 160
	ld %r16, 24(%r16)
	li %r17, 14
	mulld %r17, %r17, %r30
	add %r17, %r17, %r31
	addi %r17, %r17, 160
	ld %r17, 32(%r17)
	li %r0, 0
	rldicl %r18, %r14, 1, 63
	subf %r18, %r18, %r0
	rldicl %r19, %r15, 1, 63
	subf %r19, %r19, %r0
	rldicl %r20, %r16, 1, 63
	subf %r20, %r20, %r0
	rldicl %r21, %r17, 1, 63
	subf %r21, %r21, %r0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r22, 0
	li %r23, 0
	li %r24, 0
	li %r25, 0
	ld %r26, 0(%r5)
	ld %r27, 0(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicl %r28, %r22, 5, 59
	rldicl %r12, %r24, 5, 59
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
2438:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicr %r3, %r22, 5, 58
	add %r3, %r3, %r28
	std %r3, 0(%r5)
	rldicl %r28, %r22, 5, 59
	rldicr %r3, %r24, 5, 58
	add %r3, %r3, %r12
	std %r3, 0(%r6)
	rldicl %r12, %r24, 5, 59
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2438b
	rldicl %r0, %r28, 60, 4
	rldicr %r0, %r0, 5, 58
	subf %r0, %r0, %r28
	std %r0, 0(%r5)
	rldicl %r0, %r12, 60, 4
	rldicr %r0, %r0, 5, 58
	subf %r0, %r0, %r12
	std %r0, 0(%r6)
	li %r14, 14
	mulld %r14, %r14, %r30
	add %r14, %r14, %r31
	addi %r14, %r14, 160
	ld %r14, 8(%r14)
	li %r15, 14
	mulld %r15, %r15, %r30
	add %r15, %r15, %r31
	addi %r15, %r15, 160
	ld %r15, 16(%r15)
	li %r16, 14
	mulld %r16, %r16, %r30
	add %r16, %r16, %r31
	addi %r16, %r16, 160
	ld %r16, 24(%r16)
	li %r17, 14
	mulld %r17, %r17, %r30
	add %r17, %r17, %r31
	addi %r17, %r17, 160
	ld %r17, 32(%r17)
	li %r0, 0
	rldicl %r18, %r14, 1, 63
	subf %r18, %r18, %r0
	rldicl %r19, %r15, 1, 63
	subf %r19, %r19, %r0
	rldicl %r20, %r16, 1, 63
	subf %r20, %r20, %r0
	rldicl %r21, %r17, 1, 63
	subf %r21, %r21, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r22, 0
	li %r23, 0
	li %r24, 0
	li %r25, 0
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	ld %r4, 40(%r4)
	li %r9, 0
	li %r11, 0
	ld %r26, 0(%r5)
	ld %r27, 0(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	mulld %r28, %r22, %r4
	mulld %r12, %r24, %r4
	ld %r4, 0(%r7)
	mulld %r3, %r28, %r4
	addc %r3, %r3, %r22
	mulhdu %r0, %r28, %r4
	addze %r0, %r0
	addc %r22, %r3, %r9
	addze %r9, %r0
	mulld %r3, %r12, %r4
	addc %r3, %r3, %r24
	mulhdu %r0, %r12, %r4
	addze %r0, %r0
	addc %r24, %r3, %r11
	addze %r11, %r0
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	beq %cr0, 2439f
2441:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	ld %r4, 8(%r7)
	mulld %r3, %r28, %r4
	addc %r3, %r3, %r22
	mulhdu %r0, %r28, %r4
	addze %r0, %r0
	addc %r22, %r3, %r9
	addze %r9, %r0
	std %r22, 0(%r5)
	mulld %r3, %r12, %r4
	addc %r3, %r3, %r24
	mulhdu %r0, %r12, %r4
	addze %r0, %r0
	addc %r24, %r3, %r11
	addze %r11, %r0
	std %r24, 0(%r6)
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2441b
	b 2440f
2439:
2440:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicl %r3, %r22, 1, 63
	li %r4, 0
	subf %r3, %r3, %r4
	addc %r22, %r22, %r9
	addze %r3, %r3
	std %r22, 0(%r5)
	std %r3, 8(%r5)
	rldicl %r3, %r24, 1, 63
	subf %r3, %r3, %r4
	addc %r24, %r24, %r11
	addze %r3, %r3
	std %r24, 0(%r6)
	std %r3, 8(%r6)
	li %r3, 11
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r14, 0(%r3)
	ld %r15, 8(%r3)
	ld %r16, 16(%r3)
	ld %r17, 24(%r3)
	ld %r18, 32(%r3)
	ld %r19, 40(%r3)
	li %r3, 12
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r20, 0(%r3)
	ld %r21, 8(%r3)
	ld %r22, 16(%r3)
	ld %r23, 24(%r3)
	ld %r24, 32(%r3)
	ld %r25, 40(%r3)
	li %r3, 13
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r26, 0(%r3)
	ld %r27, 8(%r3)
	ld %r28, 16(%r3)
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 2437b
	li %r11, 1
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r9, 0
2442:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2442b
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
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
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
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
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2445:
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
	bne %cr0, 2445b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2446:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2446b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2447:
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
	bne %cr0, 2447b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2448:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2448b
	li %r9, 0
	adde %r9, %r9, %r9
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2449:
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
	bne %cr0, 2449b
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r3, %r8, 4, 59
	subf %r3, %r8, %r3
	addi %r3, %r3, 10
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
2450:
	li %r11, 1
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r9, 0
2451:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2451b
	li %r5, 11
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
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2452:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2452b
	li %r9, 0
	adde %r9, %r9, %r9
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2453:
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
	bne %cr0, 2453b
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 2450b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 2
	li %r0, 0
2454:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2454b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2455:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2455b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2456:
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
	bne %cr0, 2456b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 2
	li %r0, 0
2457:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2457b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2458:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2458b
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
	beq %cr0, 2459f
	addi %r8, %r29, 0
2461:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2461b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 112(%r31)
	b 2460f
2459:
	rldicl %r8, %r29, 63, 1
2462:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2462b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 112(%r31)
2460:
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
	beq %cr0, 2463f
	addi %r8, %r29, 0
2465:
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
	bne %cr0, 2465b
	b 2464f
2463:
	rldicl %r8, %r29, 63, 1
2466:
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
	bne %cr0, 2466b
2464:
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
	beq %cr0, 2467f
	addi %r8, %r29, 0
	li %r9, 0
2469:
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
	bne %cr0, 2469b
	b 2468f
2467:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2470:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2470b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2468:
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
	beq %cr0, 2471f
	addi %r8, %r29, 0
	li %r9, 0
2473:
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
	bne %cr0, 2473b
	b 2472f
2471:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2474:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2474b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2472:
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
	beq %cr0, 2475f
	addi %r8, %r29, 0
2477:
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
	bne %cr0, 2477b
	b 2476f
2475:
	rldicl %r8, %r29, 63, 1
2478:
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
	bne %cr0, 2478b
2476:
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
	beq %cr0, 2479f
	addi %r8, %r29, 0
2481:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2481b
	b 2480f
2479:
	rldicl %r8, %r29, 63, 1
2482:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2482b
2480:
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
	beq %cr0, 2483f
	addi %r8, %r29, 0
2485:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2485b
	b 2484f
2483:
	rldicl %r8, %r29, 63, 1
2486:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2486b
2484:
	rldicl %r11, %r22, 62, 2
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	addi %r10, %r11, 0
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
2487:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2487b
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	li %r0, 0
	std %r0, 0(%r6)
	li %r4, 2
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	ld %r5, 0(%r4)
	addi %r6, %r5, 0
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	mulld %r3, %r5, %r6
	li %r4, 2
	subf %r3, %r3, %r4
	mulld %r6, %r6, %r3
	li %r3, 0
	subf %r12, %r6, %r3
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	std %r12, 40(%r4)
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2488:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2488b
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r11, 0(%r5)
	li %r0, 1
	and %r11, %r11, %r0
	xor %r11, %r11, %r0
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	li %r9, 0
2489:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2489b
	std %r9, 0(%r5)
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r0, 0
2490:
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2490b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r0, 0
2491:
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2491b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	std %r0, 0(%r5)
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	std %r0, 0(%r5)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	add %r3, %r8, %r8
	add %r3, %r3, %r8
	addi %r3, %r3, 2
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
2492:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r4, 0(%r5)
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	ld %r5, 0(%r5)
	li %r3, 14
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r3, 0(%r3)
	li %r6, 1
	li %r7, 0
	li %r8, 0
	li %r9, 1
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	rldicr %r0, %r5, 63, 0
	rldicl %r0, %r0, 1, 63
	li %r11, 0
	subf %r11, %r0, %r11
	rldicl %r12, %r3, 1, 63
	addi %r12, %r12, -1
	and %r12, %r12, %r11
	xor %r0, %r4, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r5, %r5, %r0
	xor %r0, %r6, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r8, %r8, %r0
	xor %r0, %r7, %r12
	subf %r0, %r12, %r0
	and %r0, %r0, %r11
	add %r9, %r9, %r0
	xor %r3, %r3, %r12
	subf %r3, %r12, %r3
	addi %r3, %r3, 2
	and %r0, %r5, %r12
	add %r4, %r4, %r0
	rldicl %r5, %r5, 63, 1
	and %r0, %r8, %r12
	add %r6, %r6, %r0
	add %r6, %r6, %r6
	and %r0, %r9, %r12
	add %r7, %r7, %r0
	add %r7, %r7, %r7
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	std %r3, 0(%r4)
	std %r6, 8(%r4)
	std %r7, 16(%r4)
	std %r8, 24(%r4)
	std %r9, 32(%r4)
	li %r3, 11
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r14, 0(%r3)
	std %r15, 8(%r3)
	std %r16, 16(%r3)
	std %r17, 24(%r3)
	std %r18, 32(%r3)
	std %r19, 40(%r3)
	li %r3, 12
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r20, 0(%r3)
	std %r21, 8(%r3)
	std %r22, 16(%r3)
	std %r23, 24(%r3)
	std %r24, 32(%r3)
	std %r25, 40(%r3)
	li %r3, 13
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	std %r26, 0(%r3)
	std %r27, 8(%r3)
	std %r28, 16(%r3)
	li %r14, 14
	mulld %r14, %r14, %r30
	add %r14, %r14, %r31
	addi %r14, %r14, 160
	ld %r14, 8(%r14)
	li %r15, 14
	mulld %r15, %r15, %r30
	add %r15, %r15, %r31
	addi %r15, %r15, 160
	ld %r15, 16(%r15)
	li %r16, 14
	mulld %r16, %r16, %r30
	add %r16, %r16, %r31
	addi %r16, %r16, 160
	ld %r16, 24(%r16)
	li %r17, 14
	mulld %r17, %r17, %r30
	add %r17, %r17, %r31
	addi %r17, %r17, 160
	ld %r17, 32(%r17)
	li %r0, 0
	rldicl %r18, %r14, 1, 63
	subf %r18, %r18, %r0
	rldicl %r19, %r15, 1, 63
	subf %r19, %r19, %r0
	rldicl %r20, %r16, 1, 63
	subf %r20, %r20, %r0
	rldicl %r21, %r17, 1, 63
	subf %r21, %r21, %r0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r22, 0
	li %r23, 0
	li %r24, 0
	li %r25, 0
	ld %r26, 0(%r5)
	ld %r27, 0(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicl %r28, %r22, 5, 59
	rldicl %r12, %r24, 5, 59
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
2493:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicr %r3, %r22, 5, 58
	add %r3, %r3, %r28
	std %r3, 0(%r5)
	rldicl %r28, %r22, 5, 59
	rldicr %r3, %r24, 5, 58
	add %r3, %r3, %r12
	std %r3, 0(%r6)
	rldicl %r12, %r24, 5, 59
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2493b
	rldicl %r0, %r28, 60, 4
	rldicr %r0, %r0, 5, 58
	subf %r0, %r0, %r28
	std %r0, 0(%r5)
	rldicl %r0, %r12, 60, 4
	rldicr %r0, %r0, 5, 58
	subf %r0, %r0, %r12
	std %r0, 0(%r6)
	li %r14, 14
	mulld %r14, %r14, %r30
	add %r14, %r14, %r31
	addi %r14, %r14, 160
	ld %r14, 8(%r14)
	li %r15, 14
	mulld %r15, %r15, %r30
	add %r15, %r15, %r31
	addi %r15, %r15, 160
	ld %r15, 16(%r15)
	li %r16, 14
	mulld %r16, %r16, %r30
	add %r16, %r16, %r31
	addi %r16, %r16, 160
	ld %r16, 24(%r16)
	li %r17, 14
	mulld %r17, %r17, %r30
	add %r17, %r17, %r31
	addi %r17, %r17, 160
	ld %r17, 32(%r17)
	li %r0, 0
	rldicl %r18, %r14, 1, 63
	subf %r18, %r18, %r0
	rldicl %r19, %r15, 1, 63
	subf %r19, %r19, %r0
	rldicl %r20, %r16, 1, 63
	subf %r20, %r20, %r0
	rldicl %r21, %r17, 1, 63
	subf %r21, %r21, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r22, 0
	li %r23, 0
	li %r24, 0
	li %r25, 0
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	ld %r4, 40(%r4)
	li %r9, 0
	li %r11, 0
	ld %r26, 0(%r5)
	ld %r27, 0(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	mulld %r28, %r22, %r4
	mulld %r12, %r24, %r4
	ld %r4, 0(%r7)
	mulld %r3, %r28, %r4
	addc %r3, %r3, %r22
	mulhdu %r0, %r28, %r4
	addze %r0, %r0
	addc %r22, %r3, %r9
	addze %r9, %r0
	mulld %r3, %r12, %r4
	addc %r3, %r3, %r24
	mulhdu %r0, %r12, %r4
	addze %r0, %r0
	addc %r24, %r3, %r11
	addze %r11, %r0
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	beq %cr0, 2494f
2496:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	ld %r4, 8(%r7)
	mulld %r3, %r28, %r4
	addc %r3, %r3, %r22
	mulhdu %r0, %r28, %r4
	addze %r0, %r0
	addc %r22, %r3, %r9
	addze %r9, %r0
	std %r22, 0(%r5)
	mulld %r3, %r12, %r4
	addc %r3, %r3, %r24
	mulhdu %r0, %r12, %r4
	addze %r0, %r0
	addc %r24, %r3, %r11
	addze %r11, %r0
	std %r24, 0(%r6)
	addi %r22, %r23, 0
	rldicl %r0, %r23, 1, 63
	li %r23, 0
	subf %r23, %r0, %r23
	addi %r24, %r25, 0
	rldicl %r0, %r25, 1, 63
	li %r25, 0
	subf %r25, %r0, %r25
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2496b
	b 2495f
2494:
2495:
	ld %r26, 8(%r5)
	ld %r27, 8(%r6)
	mulld %r3, %r14, %r26
	addc %r22, %r22, %r3
	mulhdu %r3, %r14, %r26
	adde %r23, %r23, %r3
	and %r3, %r18, %r26
	subf %r23, %r3, %r23
	mulld %r3, %r15, %r27
	addc %r22, %r22, %r3
	mulhdu %r3, %r15, %r27
	adde %r23, %r23, %r3
	and %r3, %r19, %r27
	subf %r23, %r3, %r23
	mulld %r3, %r16, %r26
	addc %r24, %r24, %r3
	mulhdu %r3, %r16, %r26
	adde %r25, %r25, %r3
	and %r3, %r20, %r26
	subf %r25, %r3, %r25
	mulld %r3, %r17, %r27
	addc %r24, %r24, %r3
	mulhdu %r3, %r17, %r27
	adde %r25, %r25, %r3
	and %r3, %r21, %r27
	subf %r25, %r3, %r25
	rldicl %r3, %r22, 1, 63
	li %r4, 0
	subf %r3, %r3, %r4
	addc %r22, %r22, %r9
	addze %r3, %r3
	std %r22, 0(%r5)
	std %r3, 8(%r5)
	rldicl %r3, %r24, 1, 63
	subf %r3, %r3, %r4
	addc %r24, %r24, %r11
	addze %r3, %r3
	std %r24, 0(%r6)
	std %r3, 8(%r6)
	li %r3, 11
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r14, 0(%r3)
	ld %r15, 8(%r3)
	ld %r16, 16(%r3)
	ld %r17, 24(%r3)
	ld %r18, 32(%r3)
	ld %r19, 40(%r3)
	li %r3, 12
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r20, 0(%r3)
	ld %r21, 8(%r3)
	ld %r22, 16(%r3)
	ld %r23, 24(%r3)
	ld %r24, 32(%r3)
	ld %r25, 40(%r3)
	li %r3, 13
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r26, 0(%r3)
	ld %r27, 8(%r3)
	ld %r28, 16(%r3)
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 2492b
	li %r11, 1
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r9, 0
2497:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2497b
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2498:
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
	bne %cr0, 2498b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
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
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2500:
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
	bne %cr0, 2500b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2501:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2501b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2502:
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
	bne %cr0, 2502b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2503:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2503b
	li %r9, 0
	adde %r9, %r9, %r9
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2504:
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
	bne %cr0, 2504b
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r3, %r8, 4, 59
	subf %r3, %r8, %r3
	addi %r3, %r3, 10
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
2505:
	li %r11, 1
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	li %r9, 0
2506:
	ld %r0, 0(%r7)
	mulld %r3, %r11, %r0
	mulhdu %r0, %r11, %r0
	ld %r12, 0(%r6)
	addc %r3, %r3, %r12
	addze %r0, %r0
	addc %r3, %r3, %r9
	addze %r9, %r0
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2506b
	li %r5, 11
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
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
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
	addi %r9, %r9, -1
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 13
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2508:
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
	bne %cr0, 2508b
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 2505b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 2
	li %r0, 0
2509:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2509b
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 4
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
	subfc %r0, %r8, %r8
2510:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2510b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	rldicr %r8, %r8, 3, 60
	add %r6, %r6, %r8
	ld %r9, 0(%r6)
	rldicl %r9, %r9, 1, 63
	li %r0, 0
	subf %r9, %r9, %r0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2511:
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
	bne %cr0, 2511b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 2
	li %r0, 0
2512:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2512b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	rldicl %r8, %r8, 63, 1
	addi %r8, %r8, 1
2513:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2513b
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
	beq %cr0, 2514f
	addi %r8, %r29, 0
2516:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2516b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 116(%r31)
	b 2515f
2514:
	rldicl %r8, %r29, 63, 1
2517:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2517b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 116(%r31)
2515:
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
	beq %cr0, 2518f
	addi %r8, %r29, 0
2520:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2520b
	b 2519f
2518:
	rldicl %r8, %r29, 63, 1
2521:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2521b
2519:
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
	beq %cr0, 2522f
	addi %r8, %r29, 0
2524:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2524b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 120(%r31)
	b 2523f
2522:
	rldicl %r8, %r29, 63, 1
2525:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2525b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 120(%r31)
2523:
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
	beq %cr0, 2526f
	addi %r8, %r29, 0
2528:
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
	bne %cr0, 2528b
	b 2527f
2526:
	rldicl %r8, %r29, 63, 1
2529:
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
	bne %cr0, 2529b
2527:
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
	beq %cr0, 2530f
	addi %r8, %r29, 0
2532:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2532b
	b 2531f
2530:
	rldicl %r8, %r29, 63, 1
2533:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2533b
2531:
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
	beq %cr0, 2534f
	addi %r8, %r29, 0
2536:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2536b
	b 2535f
2534:
	rldicl %r8, %r29, 63, 1
2537:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2537b
2535:
	li %r5, 50
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2538:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2538b
	rldicr %r4, %r29, 5, 58
2539:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2540f
	addi %r8, %r29, 0
2542:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2542b
	b 2541f
2540:
	rldicl %r8, %r29, 63, 1
2543:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2543b
2541:
	li %r5, 50
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2544f
	addi %r8, %r29, 1
2546:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2546b
	b 2545f
2544:
	rldicl %r8, %r29, 63, 1
2547:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2547b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2545:
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
	beq %cr0, 2548f
	addi %r8, %r29, 1
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
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2549:
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
	beq %cr0, 2552f
	addi %r8, %r29, 1
2554:
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
	bne %cr0, 2554b
	b 2553f
2552:
	rldicl %r8, %r29, 63, 1
2555:
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
	bne %cr0, 2555b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2553:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2539b
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
	beq %cr0, 2556f
	addi %r8, %r29, 0
2558:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2558b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 120(%r31)
	b 2557f
2556:
	rldicl %r8, %r29, 63, 1
2559:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2559b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 120(%r31)
2557:
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
	beq %cr0, 2560f
	addi %r8, %r29, 0
2562:
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
	bne %cr0, 2562b
	b 2561f
2560:
	rldicl %r8, %r29, 63, 1
2563:
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
	bne %cr0, 2563b
2561:
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
	beq %cr0, 2564f
	addi %r8, %r29, 0
2566:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2566b
	b 2565f
2564:
	rldicl %r8, %r29, 63, 1
2567:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2567b
2565:
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
	beq %cr0, 2568f
	addi %r8, %r29, 0
2570:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2570b
	b 2569f
2568:
	rldicl %r8, %r29, 63, 1
2571:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2571b
2569:
	li %r5, 51
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2572:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2572b
	rldicr %r4, %r29, 5, 58
2573:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2574f
	addi %r8, %r29, 0
2576:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2576b
	b 2575f
2574:
	rldicl %r8, %r29, 63, 1
2577:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2577b
2575:
	li %r5, 51
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2578f
	addi %r8, %r29, 1
2580:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2580b
	b 2579f
2578:
	rldicl %r8, %r29, 63, 1
2581:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2581b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2579:
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
	beq %cr0, 2582f
	addi %r8, %r29, 1
	li %r9, 0
2584:
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
	bne %cr0, 2584b
	b 2583f
2582:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2585:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2585b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2583:
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
	beq %cr0, 2586f
	addi %r8, %r29, 1
2588:
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
	bne %cr0, 2588b
	b 2587f
2586:
	rldicl %r8, %r29, 63, 1
2589:
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
	bne %cr0, 2589b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2587:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2573b
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
	beq %cr0, 2590f
	addi %r8, %r29, 0
2592:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2592b
	b 2591f
2590:
	rldicl %r8, %r29, 63, 1
2593:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2593b
2591:
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
	beq %cr0, 2594f
	addi %r8, %r29, 0
2596:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2596b
	b 2595f
2594:
	rldicl %r8, %r29, 63, 1
2597:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2597b
2595:
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
	beq %cr0, 2598f
	addi %r8, %r29, 0
2600:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2600b
	b 2599f
2598:
	rldicl %r8, %r29, 63, 1
2601:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2601b
2599:
	rldicr %r11, %r22, 3, 60
2602:
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
	beq %cr0, 2603f
	addi %r8, %r29, 0
2605:
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
	bne %cr0, 2605b
	b 2604f
2603:
	rldicl %r8, %r29, 63, 1
2606:
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
	bne %cr0, 2606b
2604:
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
	beq %cr0, 2607f
	addi %r8, %r29, 0
	li %r9, 0
2609:
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
	bne %cr0, 2609b
	b 2608f
2607:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2610:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2610b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2608:
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
	beq %cr0, 2611f
	addi %r8, %r29, 0
	li %r9, 0
2613:
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
	bne %cr0, 2613b
	b 2612f
2611:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2614:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2614b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2612:
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
	beq %cr0, 2615f
	addi %r8, %r29, 0
	li %r9, 0
2617:
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
	bne %cr0, 2617b
	b 2616f
2615:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2618:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2618b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2616:
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
	beq %cr0, 2619f
	addi %r8, %r29, 0
	li %r9, 0
2621:
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
	bne %cr0, 2621b
	b 2620f
2619:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2622:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2622b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2620:
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
	beq %cr0, 2623f
	addi %r8, %r29, 0
2625:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2625b
	b 2624f
2623:
	rldicl %r8, %r29, 63, 1
2626:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2626b
2624:
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 2602b
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
	beq %cr0, 2627f
	addi %r8, %r29, 0
2629:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2629b
	b 2628f
2627:
	rldicl %r8, %r29, 63, 1
2630:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2630b
2628:
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
	beq %cr0, 2631f
	addi %r8, %r29, 0
	li %r9, 0
2633:
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
	bne %cr0, 2633b
	b 2632f
2631:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2634:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2634b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2632:
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
	beq %cr0, 2635f
	addi %r8, %r29, 0
	li %r9, 0
2637:
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
	bne %cr0, 2637b
	b 2636f
2635:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2638:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2638b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2636:
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
2639:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2639b
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
2640:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2640b
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
2641:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2641b
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
2642:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2642b
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
2643:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2643b
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
2644:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2644b
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
2645:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2645b
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
