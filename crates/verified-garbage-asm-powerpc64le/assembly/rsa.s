// The functions of `src/rsa.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_public_precompute:
	std %r14, 128(%r7)
	std %r15, 136(%r7)
	std %r16, 144(%r7)
	std %r17, 152(%r7)
	std %r18, 160(%r7)
	std %r19, 168(%r7)
	std %r20, 176(%r7)
	std %r22, 184(%r7)
	std %r21, 192(%r7)
	addi %r21, %r7, 0
	addi %r19, %r3, 0
	addi %r12, %r5, 0
	addi %r11, %r6, 7
	rldicl %r11, %r11, 61, 3
	std %r11, 48(%r21)
	rldicr %r4, %r11, 3, 60
	addi %r4, %r4, 16
	addi %r10, %r21, 256
	add %r5, %r10, %r4
	add %r8, %r5, %r4
	add %r9, %r8, %r4
	rldicr %r11, %r11, 1, 62
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
	addi %r14, %r19, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
28:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 28b
	rldicl %r17, %r11, 63, 1
	li %r0, 0
29:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 29b
	li %r3, 0
	b 27f
26:
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
210:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 210b
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	addi %r14, %r14, -8
	li %r0, 1
	std %r0, 0(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r4, %r4, 64
211:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
212:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 212b
	stw %r20, 0(%r14)
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
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
214:
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
	bne %cr0, 214b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 211b
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
	addi %r21, %r19, 0
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
215:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 215b
216:
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
	beq %cr0, 217f
219:
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
	bne %cr0, 219b
	b 218f
217:
218:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 220f
222:
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
	bne %cr0, 222b
	b 221f
220:
221:
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
	bne %cr0, 216b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
223:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 223b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
224:
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
	bne %cr0, 224b
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
225:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 225b
226:
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
	beq %cr0, 227f
229:
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
	bne %cr0, 229b
	b 228f
227:
228:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 230f
232:
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
	bne %cr0, 232b
	b 231f
230:
231:
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
	bne %cr0, 226b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
233:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 233b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
234:
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
	bne %cr0, 234b
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
235:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 235b
236:
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
	beq %cr0, 237f
239:
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
	bne %cr0, 239b
	b 238f
237:
238:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 240f
242:
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
	bne %cr0, 242b
	b 241f
240:
241:
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
	bne %cr0, 236b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
243:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 243b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
244:
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
	bne %cr0, 244b
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
245:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 245b
246:
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
	beq %cr0, 247f
249:
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
	bne %cr0, 249b
	b 248f
247:
248:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 250f
252:
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
	bne %cr0, 252b
	b 251f
250:
251:
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
	bne %cr0, 246b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
253:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 253b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
254:
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
	bne %cr0, 254b
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
255:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 255b
256:
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
	beq %cr0, 257f
259:
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
	bne %cr0, 259b
	b 258f
257:
258:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 260f
262:
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
	bne %cr0, 262b
	b 261f
260:
261:
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
	bne %cr0, 256b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
263:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 263b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
264:
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
	bne %cr0, 264b
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
265:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 265b
266:
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
	beq %cr0, 267f
269:
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
	bne %cr0, 269b
	b 268f
267:
268:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 270f
272:
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
	bne %cr0, 272b
	b 271f
270:
271:
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
	bne %cr0, 266b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
273:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 273b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
274:
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
	bne %cr0, 274b
	addi %r19, %r21, 0
	addi %r21, %r10, -256
	rldicr %r3, %r11, 2, 61
	addi %r3, %r3, 16
	addi %r5, %r10, 0
	add %r5, %r5, %r3
	addi %r8, %r10, 0
	add %r8, %r8, %r3
	add %r8, %r8, %r3
	addi %r9, %r10, 0
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	add %r9, %r9, %r3
	addi %r14, %r19, 0
	addi %r15, %r10, 0
	rldicl %r17, %r11, 63, 1
275:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 275b
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
276:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 276b
	li %r3, 1
27:
	ld %r14, 128(%r21)
	ld %r15, 136(%r21)
	ld %r16, 144(%r21)
	ld %r17, 152(%r21)
	ld %r18, 160(%r21)
	ld %r19, 168(%r21)
	ld %r20, 176(%r21)
	ld %r22, 184(%r21)
	ld %r21, 192(%r21)
	blr

vg_rsa_public_precomputed_checked:
	addi %r11, %r1, 96
	ld %r11, 0(%r11)
	std %r14, 128(%r11)
	std %r15, 136(%r11)
	std %r16, 144(%r11)
	std %r17, 152(%r11)
	std %r18, 160(%r11)
	std %r19, 168(%r11)
	std %r20, 176(%r11)
	std %r21, 184(%r11)
	std %r22, 192(%r11)
	std %r24, 200(%r11)
	std %r25, 208(%r11)
	std %r26, 216(%r11)
	std %r27, 224(%r11)
	std %r28, 232(%r11)
	std %r29, 240(%r11)
	std %r23, 248(%r11)
	addi %r23, %r11, 0
	addi %r27, %r3, 0
	addi %r28, %r4, 0
	addi %r11, %r4, 7
	rldicl %r11, %r11, 61, 3
	rldicr %r29, %r11, 3, 60
	addi %r29, %r29, 16
	addi %r10, %r23, 256
	rldicr %r11, %r11, 1, 62
	li %r24, 0
20:
	lbz %r0, 0(%r7)
	rldicr %r24, %r24, 8, 55
	or %r24, %r24, %r0
	rldicl %r3, %r24, 31, 33
	li %r4, 0
	subf %r3, %r3, %r4
	rldicl %r3, %r3, 1, 63
	subf %r3, %r3, %r4
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	xor %r0, %r24, %r4
	and %r0, %r0, %r3
	xor %r24, %r24, %r0
	addi %r7, %r7, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	li %r4, 1
	and %r0, %r24, %r4
	addi %r3, %r24, -3
	rldicl %r3, %r3, 1, 63
	xor %r3, %r3, %r4
	and %r0, %r0, %r3
	rldicr %r3, %r4, 33, 30
	subf %r3, %r3, %r24
	rldicl %r3, %r3, 1, 63
	and %r0, %r0, %r3
	li %r3, 0
	subf %r26, %r0, %r3
	rldicr %r24, %r24, 31, 32
	addi %r14, %r10, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
21:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 21b
	add %r14, %r10, %r29
	rldicl %r17, %r11, 63, 1
22:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 22b
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r12, %r9, 0
	addi %r6, %r28, 0
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
23:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 23b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
24:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 24b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r23, 256
	ld %r0, 0(%r10)
	li %r3, 1
	or %r0, %r0, %r3
	std %r0, 0(%r10)
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r10
	addi %r14, %r14, -8
	ld %r0, 0(%r14)
	rldicl %r3, %r0, 63, 1
	li %r4, 1
	and %r4, %r0, %r4
	or %r3, %r3, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r0, %r0, %r3
	std %r0, 0(%r14)
	add %r14, %r10, %r29
	rldicr %r3, %r11, 2, 61
	add %r3, %r14, %r3
	li %r0, 0
	std %r0, 0(%r3)
	addi %r8, %r10, 0
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
25:
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
	bne %cr0, 25b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
26:
	ld %r0, 0(%r14)
	and %r0, %r0, %r20
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 26b
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
27:
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
	bne %cr0, 27b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	and %r26, %r26, %r20
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
28:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 28b
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
29:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 29b
210:
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
	beq %cr0, 211f
213:
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
	bne %cr0, 213b
	b 212f
211:
212:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 214f
216:
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
	bne %cr0, 216b
	b 215f
214:
215:
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
	bne %cr0, 210b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
217:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 217b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
218:
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
	bne %cr0, 218b
	li %r25, 33
219:
	rldicl %r3, %r24, 1, 63
	rldicr %r24, %r24, 1, 62
	addi %r25, %r25, -1
	addi %r3, %r3, -1
	and %r3, %r3, %r25
	cmpldi %cr0, %r3, 0
	bne %cr0, 219b
	li %r0, 1
	li %r3, 0
	subf %r20, %r0, %r3
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
	add %r5, %r5, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
220:
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
	bne %cr0, 220b
	cmpldi %cr0, %r25, 0
	bne %cr0, 221f
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
223:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 223b
224:
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
	beq %cr0, 225f
227:
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
	bne %cr0, 227b
	b 226f
225:
226:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 228f
230:
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
	bne %cr0, 230b
	b 229f
228:
229:
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
	bne %cr0, 224b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
231:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 231b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
232:
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
	bne %cr0, 232b
	b 222f
221:
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 233f
	b 234f
233:
235:
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
	rldicl %r3, %r24, 1, 63
	rldicr %r24, %r24, 1, 62
	cmpldi %cr0, %r3, 0
	bne %cr0, 246f
	b 247f
246:
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
248:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 248b
249:
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
	beq %cr0, 250f
252:
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
	bne %cr0, 252b
	b 251f
250:
251:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 253f
255:
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
	bne %cr0, 255b
	b 254f
253:
254:
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
	bne %cr0, 249b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
256:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 256b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
257:
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
	bne %cr0, 257b
247:
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 235b
234:
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
258:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 258b
259:
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
	beq %cr0, 260f
262:
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
	bne %cr0, 262b
	b 261f
260:
261:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 263f
265:
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
	bne %cr0, 265b
	b 264f
263:
264:
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
	bne %cr0, 259b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
266:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 266b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
267:
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
	bne %cr0, 267b
	rldicl %r3, %r24, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 268f
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
270:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 270b
271:
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
	beq %cr0, 272f
274:
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
	bne %cr0, 274b
	b 273f
272:
273:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 275f
277:
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
	bne %cr0, 277b
	b 276f
275:
276:
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
	bne %cr0, 271b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
278:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 278b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
279:
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
	bne %cr0, 279b
	b 269f
268:
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
280:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 280b
281:
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
	beq %cr0, 282f
284:
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
	bne %cr0, 284b
	b 283f
282:
283:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 285f
287:
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
	bne %cr0, 287b
	b 286f
285:
286:
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
	bne %cr0, 281b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
288:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 288b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
289:
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
	bne %cr0, 289b
269:
222:
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r28
	addi %r15, %r15, -1
	addi %r16, %r27, 0
	addi %r17, %r28, 0
290:
	lbz %r0, 0(%r15)
	and %r0, %r0, %r26
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 290b
	li %r3, 1
	and %r3, %r3, %r26
	ld %r14, 128(%r23)
	ld %r15, 136(%r23)
	ld %r16, 144(%r23)
	ld %r17, 152(%r23)
	ld %r18, 160(%r23)
	ld %r19, 168(%r23)
	ld %r20, 176(%r23)
	ld %r21, 184(%r23)
	ld %r22, 192(%r23)
	ld %r24, 200(%r23)
	ld %r25, 208(%r23)
	ld %r26, 216(%r23)
	ld %r27, 224(%r23)
	ld %r28, 232(%r23)
	ld %r29, 240(%r23)
	ld %r23, 248(%r23)
	blr

vg_rsa_private_crt:
	addi %r11, %r1, 160
	ld %r11, 0(%r11)
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
	std %r3, 0(%r23)
	std %r5, 8(%r23)
	std %r6, 16(%r23)
	std %r7, 24(%r23)
	std %r9, 32(%r23)
	std %r10, 40(%r23)
	addi %r11, %r1, 96
	ld %r0, 0(%r11)
	std %r0, 48(%r23)
	ld %r0, 8(%r11)
	std %r0, 56(%r23)
	ld %r0, 16(%r11)
	std %r0, 64(%r23)
	ld %r0, 32(%r11)
	std %r0, 72(%r23)
	ld %r0, 48(%r11)
	std %r0, 80(%r23)
	addi %r4, %r6, 7
	rldicl %r4, %r4, 61, 3
	rldicr %r4, %r4, 1, 62
	addi %r10, %r23, 256
	addi %r21, %r10, 0
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r4, 1, 62
	addi %r27, %r10, 0
	addi %r28, %r29, 0
	rldicr %r5, %r29, 3, 60
	add %r5, %r10, %r5
	std %r5, 96(%r23)
	ld %r3, 40(%r23)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	addi %r0, %r4, -2
	rldicl %r0, %r0, 1, 63
	add %r4, %r4, %r0
	rldicr %r3, %r4, 3, 60
	addi %r3, %r3, 16
	rldicr %r3, %r3, 3, 60
	add %r0, %r3, %r3
	add %r3, %r3, %r0
	addi %r3, %r3, 256
	add %r5, %r5, %r3
	std %r5, 104(%r23)
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
	li %r3, 1
	subf %r0, %r3, %r0
20:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 20b
	ld %r12, 8(%r23)
	ld %r6, 16(%r23)
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
21:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 21b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
22:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 22b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r21, 0
	ld %r12, 32(%r23)
	ld %r6, 40(%r23)
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
23:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 23b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
24:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 24b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r21, 0
	ld %r12, 48(%r23)
	ld %r6, 56(%r23)
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
25:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 25b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
26:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 26b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r21, 0
	ld %r12, 24(%r23)
	ld %r6, 16(%r23)
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
27:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 27b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
28:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 28b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r21, 0
	ld %r12, 80(%r23)
	ld %r6, 40(%r23)
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
29:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 29b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
210:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 210b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r21, 0
	ld %r12, 8(%r23)
	ld %r6, 16(%r23)
	add %r15, %r12, %r6
	addi %r15, %r15, -1
	lbz %r0, 0(%r15)
	li %r18, 1
	and %r0, %r0, %r18
	xor %r0, %r0, %r18
	lbz %r15, 0(%r12)
	cmpldi %cr0, %r15, 0
	beq %cr0, 211f
	b 212f
211:
	li %r0, 1
212:
	addi %r16, %r6, -64
	cmpldi %cr0, %r16, 0
	beq %cr0, 213f
	b 214f
213:
	rldicl %r15, %r15, 57, 7
	xor %r15, %r15, %r18
	or %r0, %r0, %r15
214:
	rldicl %r3, %r0, 63, 1
	li %r4, 1
	and %r4, %r0, %r4
	or %r3, %r3, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r4, 0
	subf %r26, %r3, %r4
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
	addi %r10, %r10, 0
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
	addi %r10, %r21, 0
	and %r26, %r26, %r20
	addi %r8, %r10, 0
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
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
216:
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
	bne %cr0, 216b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	and %r26, %r26, %r20
	li %r12, 1
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
217:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 217b
218:
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
	beq %cr0, 219f
221:
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
	bne %cr0, 221b
	b 220f
219:
220:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 222f
224:
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
	bne %cr0, 224b
	b 223f
222:
223:
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
	bne %cr0, 218b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
225:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 225b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
226:
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
	bne %cr0, 226b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
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
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	addi %r10, %r10, 0
	add %r10, %r10, %r29
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
227:
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
	bne %cr0, 227b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	addi %r24, %r20, 0
	addi %r8, %r10, 0
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
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
228:
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
	bne %cr0, 228b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	or %r0, %r24, %r20
	li %r3, 0
	addi %r3, %r3, -1
	xor %r0, %r0, %r3
	and %r26, %r26, %r0
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
229:
	ld %r0, 0(%r14)
	and %r0, %r0, %r26
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 229b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	ld %r0, 0(%r14)
	li %r3, 0
	addi %r3, %r3, -1
	xor %r3, %r3, %r26
	li %r4, 3
	and %r3, %r3, %r4
	or %r0, %r0, %r3
	std %r0, 0(%r14)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
230:
	ld %r0, 0(%r14)
	and %r0, %r0, %r26
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 230b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	ld %r0, 0(%r14)
	li %r3, 0
	addi %r3, %r3, -1
	xor %r3, %r3, %r26
	li %r4, 3
	and %r3, %r3, %r4
	or %r0, %r0, %r3
	std %r0, 0(%r14)
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
231:
	ld %r0, 0(%r14)
	and %r0, %r0, %r26
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 231b
	ld %r12, 24(%r23)
	ld %r6, 16(%r23)
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
232:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 232b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
233:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 233b
	add %r14, %r10, %r29
	addi %r14, %r14, -16
	li %r0, 0
	std %r0, 0(%r14)
	addi %r10, %r21, 0
	ld %r3, 40(%r23)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	addi %r0, %r4, -2
	rldicl %r0, %r0, 1, 63
	add %r4, %r4, %r0
	ld %r3, 96(%r23)
	addi %r10, %r3, 256
	addi %r21, %r10, 0
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r4, 1, 62
	ld %r25, 16(%r23)
	addi %r14, %r10, 0
	addi %r15, %r27, 0
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	rldicl %r17, %r11, 63, 1
234:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 234b
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
235:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 235b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 5, 58
	rldicl %r3, %r11, 63, 1
	add %r4, %r4, %r3
236:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
237:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 237b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
238:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 238b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
239:
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
	bne %cr0, 239b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 236b
	li %r24, 6
240:
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
241:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 241b
242:
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
	beq %cr0, 243f
245:
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
	bne %cr0, 245b
	b 244f
243:
244:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 246f
248:
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
	bne %cr0, 248b
	b 247f
246:
247:
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
	bne %cr0, 242b
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
	bne %cr0, 240b
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
251:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 251b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
252:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 252b
253:
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
	beq %cr0, 254f
256:
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
	bne %cr0, 256b
	b 255f
254:
255:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 257f
259:
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
	bne %cr0, 259b
	b 258f
257:
258:
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
	bne %cr0, 253b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
260:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 260b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
261:
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
	bne %cr0, 261b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
262:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 262b
	addi %r30, %r27, 0
	add %r30, %r30, %r28
	add %r30, %r30, %r28
	add %r30, %r30, %r28
	add %r30, %r30, %r28
	add %r30, %r30, %r28
	add %r30, %r30, %r28
	addi %r31, %r25, 7
	rldicl %r31, %r31, 61, 3
263:
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r30, 0
	rldicl %r17, %r11, 63, 1
264:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 264b
	addi %r30, %r15, 0
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
265:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 265b
266:
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
	beq %cr0, 267f
269:
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
	bne %cr0, 269b
	b 268f
267:
268:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 270f
272:
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
	bne %cr0, 272b
	b 271f
270:
271:
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
	bne %cr0, 266b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
273:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 273b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
274:
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
	bne %cr0, 274b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
275:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 275b
276:
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
	beq %cr0, 277f
279:
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
	bne %cr0, 279b
	b 278f
277:
278:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 280f
282:
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
	bne %cr0, 282b
	b 281f
280:
281:
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
	bne %cr0, 276b
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
285:
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
	bne %cr0, 285b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r24, 0
286:
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
	bne %cr0, 286b
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
287:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 287b
	rldicl %r3, %r11, 63, 1
	subf %r31, %r3, %r31
	addi %r3, %r31, -1
	rldicl %r3, %r3, 1, 63
	li %r0, 1
	xor %r3, %r3, %r0
	cmpldi %cr0, %r3, 0
	bne %cr0, 263b
	ld %r30, 64(%r23)
	ld %r31, 40(%r23)
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
288:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 288b
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
289:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 289b
290:
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
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 293b
	b 292f
291:
292:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 294f
296:
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
	bne %cr0, 296b
	b 295f
294:
295:
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
	bne %cr0, 290b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
299:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 299b
2100:
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
	beq %cr0, 2101f
2103:
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
	bne %cr0, 2103b
	b 2102f
2101:
2102:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2104f
2106:
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
	bne %cr0, 2106b
	b 2105f
2104:
2105:
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
	bne %cr0, 2100b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2107:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2107b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2108:
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
	bne %cr0, 2108b
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
2109:
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
	bne %cr0, 2109b
	li %r24, 2
2110:
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2111:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2111b
2112:
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
	beq %cr0, 2113f
2115:
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
	bne %cr0, 2115b
	b 2114f
2113:
2114:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2116f
2118:
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
	bne %cr0, 2118b
	b 2117f
2116:
2117:
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
	bne %cr0, 2112b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2119:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2119b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2120:
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
	bne %cr0, 2120b
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
2121:
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
	bne %cr0, 2121b
	addi %r24, %r24, 1
	addi %r4, %r24, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2110b
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
2122:
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
	bne %cr0, 2122b
2123:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2124:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2124b
2125:
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
	beq %cr0, 2126f
2128:
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
	bne %cr0, 2128b
	b 2127f
2126:
2127:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2129f
2131:
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
	bne %cr0, 2131b
	b 2130f
2129:
2130:
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
	bne %cr0, 2125b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2132:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2132b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2133:
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
	bne %cr0, 2133b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2134:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2134b
2135:
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
	beq %cr0, 2136f
2138:
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
	bne %cr0, 2138b
	b 2137f
2136:
2137:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2139f
2141:
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
	bne %cr0, 2141b
	b 2140f
2139:
2140:
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
	bne %cr0, 2135b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2142:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2142b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2144:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2144b
2145:
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
	beq %cr0, 2146f
2148:
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
	bne %cr0, 2148b
	b 2147f
2146:
2147:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2149f
2151:
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
	bne %cr0, 2151b
	b 2150f
2149:
2150:
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
	bne %cr0, 2145b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2152:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2152b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2153:
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
	bne %cr0, 2153b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2154:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2154b
2155:
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
	beq %cr0, 2156f
2158:
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
	bne %cr0, 2158b
	b 2157f
2156:
2157:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2159f
2161:
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
	bne %cr0, 2161b
	b 2160f
2159:
2160:
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
	bne %cr0, 2155b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2162:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2162b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
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
	rldicl %r18, %r24, 4, 60
	li %r19, 0
2164:
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
	addi %r19, %r19, 1
	addi %r4, %r19, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2164b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2167:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2167b
2168:
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
	beq %cr0, 2169f
2171:
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
	bne %cr0, 2171b
	b 2170f
2169:
2170:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2172f
2174:
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
	bne %cr0, 2174b
	b 2173f
2172:
2173:
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
	bne %cr0, 2168b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2175:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2175b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2176:
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
	bne %cr0, 2176b
	rldicr %r24, %r24, 4, 59
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2177:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2177b
2178:
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
	beq %cr0, 2179f
2181:
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
	bne %cr0, 2181b
	b 2180f
2179:
2180:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2182f
2184:
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
	bne %cr0, 2184b
	b 2183f
2182:
2183:
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
	bne %cr0, 2178b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2185:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2185b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2186:
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
	bne %cr0, 2186b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2187:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2187b
2188:
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
	beq %cr0, 2189f
2191:
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
	bne %cr0, 2191b
	b 2190f
2189:
2190:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2192f
2194:
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
	bne %cr0, 2194b
	b 2193f
2192:
2193:
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
	bne %cr0, 2188b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2195:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2195b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2196:
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
	bne %cr0, 2196b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2197:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2197b
2198:
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
	beq %cr0, 2199f
2201:
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
	bne %cr0, 2201b
	b 2200f
2199:
2200:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2202f
2204:
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
	bne %cr0, 2204b
	b 2203f
2202:
2203:
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
	bne %cr0, 2198b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2205:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2205b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2206:
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
	bne %cr0, 2206b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2207:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2207b
2208:
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
	beq %cr0, 2209f
2211:
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
	bne %cr0, 2211b
	b 2210f
2209:
2210:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2212f
2214:
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
	bne %cr0, 2214b
	b 2213f
2212:
2213:
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
	bne %cr0, 2208b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2215:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2215b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
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
	rldicl %r18, %r24, 4, 60
	li %r19, 0
2217:
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
2218:
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
	bne %cr0, 2218b
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
2219:
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
	bne %cr0, 2219b
	addi %r19, %r19, 1
	addi %r4, %r19, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2217b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2220:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2220b
2221:
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
	beq %cr0, 2222f
2224:
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
	bne %cr0, 2224b
	b 2223f
2222:
2223:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2225f
2227:
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
	bne %cr0, 2227b
	b 2226f
2225:
2226:
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
	bne %cr0, 2221b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2228:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2228b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2229:
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
	bne %cr0, 2229b
	rldicr %r24, %r24, 4, 59
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2123b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2230:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2230b
2231:
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
	beq %cr0, 2232f
2234:
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
	bne %cr0, 2234b
	b 2233f
2232:
2233:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2235f
2237:
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
	bne %cr0, 2237b
	b 2236f
2235:
2236:
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
	bne %cr0, 2231b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2238:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2238b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2239:
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
	bne %cr0, 2239b
	ld %r3, 56(%r23)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	addi %r0, %r4, -2
	rldicl %r0, %r0, 1, 63
	add %r4, %r4, %r0
	ld %r3, 104(%r23)
	addi %r10, %r3, 256
	addi %r21, %r10, 0
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r4, 1, 62
	ld %r25, 16(%r23)
	addi %r14, %r10, 0
	addi %r15, %r27, 0
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	rldicl %r17, %r11, 63, 1
2240:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2240b
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
2241:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2241b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 5, 58
	rldicl %r3, %r11, 63, 1
	add %r4, %r4, %r3
2242:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
2243:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2243b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2244:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2244b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2245:
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
	bne %cr0, 2245b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2242b
	li %r24, 6
2246:
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
2247:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2247b
2248:
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
	beq %cr0, 2249f
2251:
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
	bne %cr0, 2251b
	b 2250f
2249:
2250:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2252f
2254:
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
	bne %cr0, 2254b
	b 2253f
2252:
2253:
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
	bne %cr0, 2248b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2255:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2255b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2256:
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
	bne %cr0, 2256b
	addi %r24, %r24, -1
	cmpldi %cr0, %r24, 0
	bne %cr0, 2246b
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
2257:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2257b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2258:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2258b
2259:
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
	beq %cr0, 2260f
2262:
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
	bne %cr0, 2262b
	b 2261f
2260:
2261:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2263f
2265:
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
	bne %cr0, 2265b
	b 2264f
2263:
2264:
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
	bne %cr0, 2259b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2266:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2266b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2267:
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
	bne %cr0, 2267b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2268:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2268b
	addi %r30, %r27, 0
	add %r30, %r30, %r28
	add %r30, %r30, %r28
	add %r30, %r30, %r28
	add %r30, %r30, %r28
	add %r30, %r30, %r28
	add %r30, %r30, %r28
	addi %r31, %r25, 7
	rldicl %r31, %r31, 61, 3
2269:
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r30, 0
	rldicl %r17, %r11, 63, 1
2270:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2270b
	addi %r30, %r15, 0
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2271:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2271b
2272:
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
	beq %cr0, 2273f
2275:
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
	bne %cr0, 2275b
	b 2274f
2273:
2274:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2276f
2278:
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
	bne %cr0, 2278b
	b 2277f
2276:
2277:
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
	bne %cr0, 2272b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2279:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2279b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2280:
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
	bne %cr0, 2280b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2281:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2281b
2282:
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
	beq %cr0, 2283f
2285:
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
	bne %cr0, 2285b
	b 2284f
2283:
2284:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2286f
2288:
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
	bne %cr0, 2288b
	b 2287f
2286:
2287:
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
	bne %cr0, 2282b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2289:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2289b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2290:
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
	bne %cr0, 2290b
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
2291:
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
	bne %cr0, 2291b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r24, 0
2292:
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
	bne %cr0, 2292b
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
2293:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2293b
	rldicl %r3, %r11, 63, 1
	subf %r31, %r3, %r31
	addi %r3, %r31, -1
	rldicl %r3, %r3, 1, 63
	li %r0, 1
	xor %r3, %r3, %r0
	cmpldi %cr0, %r3, 0
	bne %cr0, 2269b
	ld %r30, 72(%r23)
	ld %r31, 56(%r23)
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
2294:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2294b
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
2295:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2295b
2296:
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
	beq %cr0, 2297f
2299:
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
	bne %cr0, 2299b
	b 2298f
2297:
2298:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2300f
2302:
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
	bne %cr0, 2302b
	b 2301f
2300:
2301:
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
	bne %cr0, 2296b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2303:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2303b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2304:
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
	bne %cr0, 2304b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2305:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2305b
2306:
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
	beq %cr0, 2307f
2309:
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
	bne %cr0, 2309b
	b 2308f
2307:
2308:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2310f
2312:
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
	bne %cr0, 2312b
	b 2311f
2310:
2311:
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
	bne %cr0, 2306b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2313:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2313b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2314:
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
	bne %cr0, 2314b
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
2315:
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
	bne %cr0, 2315b
	li %r24, 2
2316:
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2317:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2317b
2318:
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
	beq %cr0, 2319f
2321:
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
	bne %cr0, 2321b
	b 2320f
2319:
2320:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2322f
2324:
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
	bne %cr0, 2324b
	b 2323f
2322:
2323:
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
	bne %cr0, 2318b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2325:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2325b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2326:
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
	bne %cr0, 2326b
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
2327:
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
	bne %cr0, 2327b
	addi %r24, %r24, 1
	addi %r4, %r24, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2316b
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
2328:
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
	bne %cr0, 2328b
2329:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2330:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2330b
2331:
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
	beq %cr0, 2332f
2334:
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
	bne %cr0, 2334b
	b 2333f
2332:
2333:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2335f
2337:
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
	bne %cr0, 2337b
	b 2336f
2335:
2336:
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
	bne %cr0, 2331b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2338:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2338b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2339:
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
	bne %cr0, 2339b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2340:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2340b
2341:
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
	beq %cr0, 2342f
2344:
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
	bne %cr0, 2344b
	b 2343f
2342:
2343:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2345f
2347:
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
	bne %cr0, 2347b
	b 2346f
2345:
2346:
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
	bne %cr0, 2341b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2348:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2348b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2349:
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
	bne %cr0, 2349b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2350:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2350b
2351:
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
	beq %cr0, 2352f
2354:
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
	bne %cr0, 2354b
	b 2353f
2352:
2353:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2355f
2357:
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
	bne %cr0, 2357b
	b 2356f
2355:
2356:
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
	bne %cr0, 2351b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2358:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2358b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2359:
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
	bne %cr0, 2359b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2360:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2360b
2361:
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
	beq %cr0, 2362f
2364:
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
	bne %cr0, 2364b
	b 2363f
2362:
2363:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2365f
2367:
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
	bne %cr0, 2367b
	b 2366f
2365:
2366:
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
	bne %cr0, 2361b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2368:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2368b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2369:
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
	bne %cr0, 2369b
	rldicl %r18, %r24, 4, 60
	li %r19, 0
2370:
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
2371:
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
	bne %cr0, 2371b
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
2372:
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
	bne %cr0, 2372b
	addi %r19, %r19, 1
	addi %r4, %r19, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2370b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2373:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2373b
2374:
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
	beq %cr0, 2375f
2377:
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
	bne %cr0, 2377b
	b 2376f
2375:
2376:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2378f
2380:
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
	bne %cr0, 2380b
	b 2379f
2378:
2379:
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
	bne %cr0, 2374b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2381:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2381b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2382:
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
	bne %cr0, 2382b
	rldicr %r24, %r24, 4, 59
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2383:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2383b
2384:
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
	beq %cr0, 2385f
2387:
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
	bne %cr0, 2387b
	b 2386f
2385:
2386:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2388f
2390:
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
	bne %cr0, 2390b
	b 2389f
2388:
2389:
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
	bne %cr0, 2384b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2391:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2391b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2392:
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
	bne %cr0, 2392b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2393:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2393b
2394:
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
	beq %cr0, 2395f
2397:
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
	bne %cr0, 2397b
	b 2396f
2395:
2396:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2398f
2400:
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
	bne %cr0, 2400b
	b 2399f
2398:
2399:
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
	bne %cr0, 2394b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2401:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2401b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2402:
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
	bne %cr0, 2402b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2403:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2403b
2404:
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
	beq %cr0, 2405f
2407:
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
	bne %cr0, 2407b
	b 2406f
2405:
2406:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2408f
2410:
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
	bne %cr0, 2410b
	b 2409f
2408:
2409:
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
	bne %cr0, 2404b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2411:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2411b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2412:
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
	bne %cr0, 2412b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2413:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2413b
2414:
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
	beq %cr0, 2415f
2417:
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
	bne %cr0, 2417b
	b 2416f
2415:
2416:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2418f
2420:
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
	bne %cr0, 2420b
	b 2419f
2418:
2419:
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
	bne %cr0, 2414b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2421:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2421b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2422:
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
	bne %cr0, 2422b
	rldicl %r18, %r24, 4, 60
	li %r19, 0
2423:
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
2424:
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
	bne %cr0, 2424b
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
2425:
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
	bne %cr0, 2425b
	addi %r19, %r19, 1
	addi %r4, %r19, -16
	cmpldi %cr0, %r4, 0
	bne %cr0, 2423b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2426:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2426b
2427:
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
	beq %cr0, 2428f
2430:
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
	bne %cr0, 2430b
	b 2429f
2428:
2429:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2431f
2433:
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
	bne %cr0, 2433b
	b 2432f
2431:
2432:
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
	bne %cr0, 2427b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2434:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2434b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2435:
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
	bne %cr0, 2435b
	rldicr %r24, %r24, 4, 59
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2329b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2436:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2436b
2437:
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
	beq %cr0, 2438f
2440:
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
	bne %cr0, 2440b
	b 2439f
2438:
2439:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2441f
2443:
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
	bne %cr0, 2443b
	b 2442f
2441:
2442:
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
	bne %cr0, 2437b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2444:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2444b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2445:
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
	bne %cr0, 2445b
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	ld %r17, 56(%r23)
	add %r15, %r15, %r17
	addi %r15, %r15, -1
	addi %r16, %r27, 0
	add %r16, %r16, %r28
2446:
	lbz %r0, 0(%r15)
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2446b
	ld %r3, 40(%r23)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	addi %r0, %r4, -2
	rldicl %r0, %r0, 1, 63
	add %r4, %r4, %r0
	ld %r3, 96(%r23)
	addi %r10, %r3, 256
	addi %r21, %r10, 0
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r4, 1, 62
	ld %r31, 56(%r23)
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
2447:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2447b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 5, 58
	rldicl %r3, %r11, 63, 1
	add %r4, %r4, %r3
2448:
	li %r20, 0
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
2449:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2449b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2450:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2450b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2451:
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
	bne %cr0, 2451b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2448b
	li %r24, 6
2452:
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
2453:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2453b
2454:
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
	beq %cr0, 2455f
2457:
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
	bne %cr0, 2457b
	b 2456f
2455:
2456:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2458f
2460:
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
	bne %cr0, 2460b
	b 2459f
2458:
2459:
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
	bne %cr0, 2454b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2461:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2461b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2462:
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
	bne %cr0, 2462b
	addi %r24, %r24, -1
	cmpldi %cr0, %r24, 0
	bne %cr0, 2452b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	rldicl %r17, %r11, 63, 1
2463:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2463b
	addi %r30, %r27, 0
	add %r30, %r30, %r28
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2464:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2464b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	addi %r8, %r10, 0
	add %r8, %r8, %r29
	add %r8, %r8, %r29
	addi %r9, %r10, 0
	add %r9, %r9, %r29
	add %r9, %r9, %r29
	add %r9, %r9, %r29
2465:
	lbz %r24, 0(%r30)
	rldicr %r24, %r24, 56, 7
	addi %r30, %r30, 1
	li %r25, 8
2466:
	rldicl %r20, %r24, 1, 63
	rldicr %r24, %r24, 1, 62
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	rldicl %r17, %r11, 63, 1
2467:
	ld %r0, 0(%r15)
	rldicr %r3, %r0, 1, 62
	add %r3, %r3, %r20
	rldicl %r20, %r0, 1, 63
	std %r3, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2467b
	std %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2468:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2468b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2469:
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
	bne %cr0, 2469b
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 2466b
	addi %r31, %r31, -1
	cmpldi %cr0, %r31, 0
	bne %cr0, 2465b
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
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2470:
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
	bne %cr0, 2470b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r10, %r21, 0
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r24, 0
2471:
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
	bne %cr0, 2471b
	addi %r14, %r10, 0
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	add %r14, %r14, %r29
	addi %r15, %r27, 0
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	rldicl %r17, %r11, 63, 1
2472:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2472b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2473:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2473b
2474:
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
	beq %cr0, 2475f
2477:
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
	bne %cr0, 2477b
	b 2476f
2475:
2476:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2478f
2480:
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
	bne %cr0, 2480b
	b 2479f
2478:
2479:
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
	bne %cr0, 2474b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2481:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2481b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2482:
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
	bne %cr0, 2482b
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2483:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2483b
2484:
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
	beq %cr0, 2485f
2487:
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
	bne %cr0, 2487b
	b 2486f
2485:
2486:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2488f
2490:
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
	bne %cr0, 2490b
	b 2489f
2488:
2489:
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
	bne %cr0, 2484b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2491:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2491b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2492:
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
	bne %cr0, 2492b
	ld %r3, 40(%r23)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	addi %r0, %r4, -2
	rldicl %r0, %r0, 1, 63
	add %r4, %r4, %r0
	ld %r3, 96(%r23)
	addi %r10, %r3, 256
	addi %r21, %r10, 0
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r4, 1, 62
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r22, %r11, 0
	rldicr %r11, %r4, 1, 62
	addi %r14, %r27, 0
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	addi %r11, %r28, 0
	addi %r11, %r11, -16
	rldicl %r11, %r11, 62, 2
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2493:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2493b
	addi %r14, %r27, 0
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	addi %r11, %r22, 0
	rldicl %r17, %r11, 63, 1
2494:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2494b
	ld %r3, 56(%r23)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	addi %r0, %r4, -2
	rldicl %r0, %r0, 1, 63
	add %r4, %r4, %r0
	ld %r3, 104(%r23)
	addi %r10, %r3, 256
	addi %r21, %r10, 0
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	rldicr %r11, %r4, 1, 62
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	addi %r22, %r11, 0
	addi %r14, %r27, 0
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	addi %r11, %r28, 0
	addi %r11, %r11, -16
	rldicl %r11, %r11, 62, 2
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2495:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2495b
	addi %r14, %r27, 0
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	add %r14, %r14, %r28
	addi %r11, %r22, 0
	rldicl %r17, %r11, 63, 1
2496:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2496b
	addi %r10, %r27, 0
	addi %r21, %r27, 0
	addi %r29, %r28, 0
	addi %r11, %r28, 0
	addi %r11, %r11, -16
	rldicl %r11, %r11, 62, 2
	li %r12, 1
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2497:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2497b
2498:
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
	beq %cr0, 2499f
2501:
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
	bne %cr0, 2501b
	b 2500f
2499:
2500:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2502f
2504:
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
	bne %cr0, 2504b
	b 2503f
2502:
2503:
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
	bne %cr0, 2498b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2505:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2505b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2506:
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
	bne %cr0, 2506b
	addi %r15, %r27, 0
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	add %r15, %r15, %r28
	addi %r16, %r27, 0
	add %r16, %r16, %r28
	add %r16, %r16, %r28
	add %r16, %r16, %r28
	add %r16, %r16, %r28
	add %r16, %r16, %r28
	add %r16, %r16, %r28
	li %r20, 0
	addi %r20, %r20, -1
	addi %r17, %r11, 0
	li %r24, 0
2507:
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
	bne %cr0, 2507b
	addi %r10, %r27, 0
	addi %r29, %r28, 0
	ld %r27, 0(%r23)
	ld %r28, 16(%r23)
	addi %r15, %r10, 0
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r29
	add %r15, %r15, %r28
	addi %r15, %r15, -1
	addi %r16, %r27, 0
	addi %r17, %r28, 0
2508:
	lbz %r0, 0(%r15)
	and %r0, %r0, %r26
	stb %r0, 0(%r16)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2508b
	li %r3, 1
	and %r3, %r3, %r26
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

vg_rsa_private_checked:
	stdu %r1, -3328(%r1)
	addi %r12, %r1, 0
	std %r24, 176(%r12)
	std %r25, 184(%r12)
	std %r26, 192(%r12)
	std %r27, 200(%r12)
	std %r28, 208(%r12)
	std %r29, 216(%r12)
	mflr %r0
	std %r0, 224(%r12)
	or %r24, %r3, %r3
	or %r25, %r5, %r5
	or %r26, %r6, %r6
	or %r27, %r7, %r7
	or %r28, %r8, %r8
	or %r29, %r9, %r9
	addi %r3, %r12, 248
	or %r4, %r26, %r26
	or %r7, %r29, %r29
	or %r8, %r26, %r26
	ld %r9, 3424(%r12)
	ld %r10, 3432(%r12)
	ld %r0, 3440(%r12)
	std %r0, 96(%r12)
	ld %r0, 3448(%r12)
	std %r0, 104(%r12)
	ld %r0, 3456(%r12)
	std %r0, 112(%r12)
	ld %r0, 3464(%r12)
	std %r0, 120(%r12)
	ld %r0, 3472(%r12)
	std %r0, 128(%r12)
	ld %r0, 3480(%r12)
	std %r0, 136(%r12)
	ld %r0, 3488(%r12)
	std %r0, 144(%r12)
	ld %r0, 3496(%r12)
	std %r0, 152(%r12)
	ld %r0, 3504(%r12)
	std %r0, 160(%r12)
	ld %r0, 3512(%r12)
	std %r0, 168(%r12)
	bl {vg_rsa_private_crt}
	addi %r12, %r1, 0
	std %r3, 232(%r12)
	addi %r3, %r12, 1272
	addi %r4, %r26, 7
	rldicl %r4, %r4, 61, 3
	rldicr %r4, %r4, 1, 62
	or %r5, %r25, %r25
	or %r6, %r26, %r26
	ld %r7, 3504(%r12)
	ld %r8, 3512(%r12)
	bl {vg_rsa_public_precompute}
	addi %r12, %r1, 0
	or %r3, %r24, %r24
	or %r4, %r26, %r26
	addi %r5, %r12, 1272
	addi %r4, %r26, 7
	rldicl %r4, %r4, 61, 3
	rldicr %r4, %r4, 1, 62
	addi %r6, %r4, 0
	or %r4, %r26, %r26
	or %r7, %r27, %r27
	or %r8, %r28, %r28
	addi %r9, %r12, 248
	or %r10, %r26, %r26
	ld %r0, 3504(%r12)
	std %r0, 96(%r12)
	ld %r0, 3512(%r12)
	std %r0, 104(%r12)
	bl {vg_rsa_public_precomputed_checked}
	addi %r12, %r1, 0
	std %r3, 240(%r12)
	or %r3, %r24, %r24
	or %r4, %r29, %r29
	li %r5, 0
	or %r6, %r26, %r26
20:
	lbz %r7, 0(%r3)
	lbz %r8, 0(%r4)
	xor %r7, %r7, %r8
	or %r5, %r5, %r7
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 20b
	addi %r12, %r1, 0
	ld %r3, 232(%r12)
	ld %r4, 240(%r12)
	and %r3, %r3, %r4
	li %r4, 1
	and %r3, %r3, %r4
	addi %r5, %r5, -1
	rldicl %r5, %r5, 1, 63
	li %r4, 2
	subf %r4, %r5, %r4
	and %r5, %r5, %r3
	li %r9, 0
	subf %r9, %r5, %r9
	li %r7, 0
	subf %r3, %r3, %r7
	and %r3, %r3, %r4
	or %r6, %r26, %r26
	or %r7, %r24, %r24
	addi %r8, %r12, 248
21:
	lbz %r0, 0(%r8)
	and %r0, %r0, %r9
	stb %r0, 0(%r7)
	li %r0, 0
	stb %r0, 0(%r8)
	addi %r7, %r7, 1
	addi %r8, %r8, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 21b
	addi %r12, %r1, 0
	ld %r0, 224(%r12)
	mtlr %r0
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	addi %r1, %r1, 3328
	blr

vg_rsa_crt_values:
	addi %r11, %r1, 144
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
	addi %r18, %r10, 0
	addi %r19, %r1, 96
	ld %r19, 0(%r19)
	addi %r20, %r1, 104
	ld %r20, 0(%r20)
	addi %r21, %r1, 112
	ld %r21, 0(%r21)
	addi %r22, %r1, 120
	ld %r22, 0(%r22)
	addi %r23, %r1, 128
	ld %r23, 0(%r23)
	addi %r24, %r1, 136
	ld %r24, 0(%r24)
	add %r11, %r9, %r10
	addi %r11, %r11, -1
	lbz %r0, 0(%r11)
	li %r12, 1
	and %r0, %r0, %r12
	xor %r0, %r0, %r12
	lbz %r11, 0(%r9)
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	b 21f
20:
	li %r0, 1
21:
	addi %r12, %r10, -64
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
	b 23f
22:
	rldicl %r11, %r11, 57, 7
	li %r12, 1
	xor %r11, %r11, %r12
	or %r0, %r0, %r11
23:
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	addi %r5, %r14, 0
	addi %r8, %r20, 0
	li %r0, 0
26:
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 26b
	addi %r5, %r15, 0
	addi %r8, %r22, 0
	li %r0, 0
27:
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 27b
	addi %r5, %r16, 0
	addi %r8, %r20, 0
	li %r0, 0
28:
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 28b
	li %r3, 0
	b 25f
24:
	addi %r29, %r18, 3
	rldicl %r29, %r29, 62, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r8, 25
	mulld %r8, %r8, %r30
	rldicl %r8, %r8, 62, 2
	addi %r5, %r31, 160
	li %r0, 0
29:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 29b
	addi %r6, %r17, 0
	addi %r8, %r18, 0
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
210:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 210b
	addi %r6, %r19, 0
	addi %r8, %r20, 0
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
211:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 211b
	addi %r6, %r21, 0
	addi %r8, %r22, 0
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
212:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 212b
	addi %r6, %r23, 0
	addi %r8, %r24, 0
	li %r5, 24
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
213:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 213b
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 214f
	addi %r8, %r29, 0
216:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 216b
	b 215f
214:
	rldicl %r8, %r29, 63, 1
217:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 217b
215:
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 136(%r31)
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
218:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 218b
	rldicr %r4, %r29, 5, 58
219:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 220f
	addi %r8, %r29, 0
222:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 222b
	b 221f
220:
	rldicl %r8, %r29, 63, 1
223:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 223b
221:
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 224f
	addi %r8, %r29, 1
226:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 226b
	b 225f
224:
	rldicl %r8, %r29, 63, 1
227:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 227b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
225:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 19
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
	beq %cr0, 228f
	addi %r8, %r29, 1
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
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
229:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 19
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 232f
	addi %r8, %r29, 1
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
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
233:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 219b
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 16
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 236f
	addi %r8, %r29, 0
238:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 238b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 140(%r31)
	b 237f
236:
	rldicl %r8, %r29, 63, 1
239:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 239b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 140(%r31)
237:
	li %r6, 19
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
	beq %cr0, 240f
	addi %r8, %r29, 0
242:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 242b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 144(%r31)
	b 241f
240:
	rldicl %r8, %r29, 63, 1
243:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 243b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 144(%r31)
241:
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 16
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
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 248f
	addi %r8, %r29, 0
250:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 250b
	b 249f
248:
	rldicl %r8, %r29, 63, 1
251:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 251b
249:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	li %r5, 15
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	subf %r11, %r22, %r20
	rldicl %r0, %r11, 1, 63
	li %r3, 0
	subf %r0, %r0, %r3
	and %r11, %r11, %r0
	subf %r11, %r11, %r20
	addi %r11, %r11, 3
	rldicl %r11, %r11, 62, 2
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
252:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 252b
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	rldicr %r8, %r8, 2, 61
	add %r6, %r6, %r8
	li %r0, 0
	stw %r0, 0(%r6)
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
253:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 253b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
254:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 254b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	rldicr %r0, %r0, 1, 62
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r3, 0(%r5)
	or %r3, %r3, %r0
	stw %r3, 0(%r5)
	li %r10, 2
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
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
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	std %r12, 40(%r5)
	addi %r10, %r11, 0
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
255:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 255b
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r11, 0(%r5)
	rldicr %r11, %r11, 63, 0
	rldicl %r11, %r11, 1, 63
	li %r0, 1
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
	li %r9, 0
256:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 256b
	stw %r9, 0(%r5)
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r0, 0
257:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 257b
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	std %r0, 0(%r5)
	addi %r3, %r10, 1
	add %r0, %r3, %r3
	add %r3, %r3, %r0
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
258:
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r4, 0(%r5)
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r5, 0(%r5)
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
	li %r4, 14
	mulld %r4, %r4, %r30
	add %r4, %r4, %r31
	addi %r4, %r4, 160
	std %r3, 0(%r4)
	std %r6, 8(%r4)
	std %r7, 16(%r4)
	std %r8, 24(%r4)
	std %r9, 32(%r4)
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
	li %r11, 14
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r11, 8(%r11)
	li %r12, 14
	mulld %r12, %r12, %r30
	add %r12, %r12, %r31
	addi %r12, %r12, 160
	ld %r12, 16(%r12)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
259:
	lwz %r0, 0(%r6)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 259b
	lwz %r0, 0(%r6)
	rldicl %r4, %r0, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r0, %r4, %r0
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	rldicl %r4, %r3, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r3, %r4, %r3
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	stw %r9, 4(%r5)
	li %r5, 12
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
	li %r11, 14
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r11, 24(%r11)
	li %r12, 14
	mulld %r12, %r12, %r30
	add %r12, %r12, %r31
	addi %r12, %r12, 160
	ld %r12, 32(%r12)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
260:
	lwz %r0, 0(%r6)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 260b
	lwz %r0, 0(%r6)
	rldicl %r4, %r0, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r0, %r4, %r0
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	rldicl %r4, %r3, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r3, %r4, %r3
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	stw %r9, 4(%r5)
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
261:
	lwz %r0, 0(%r6)
	lwz %r3, 4(%r6)
	rldicl %r0, %r0, 34, 30
	rldicr %r3, %r3, 2, 61
	add %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 261b
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
262:
	lwz %r0, 0(%r6)
	lwz %r3, 4(%r6)
	rldicl %r0, %r0, 34, 30
	rldicr %r3, %r3, 2, 61
	add %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 262b
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
	li %r11, 14
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r11, 8(%r11)
	li %r12, 14
	mulld %r12, %r12, %r30
	add %r12, %r12, %r31
	addi %r12, %r12, 160
	ld %r12, 16(%r12)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
263:
	lwz %r0, 0(%r6)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 263b
	lwz %r0, 0(%r6)
	rldicl %r4, %r0, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r0, %r4, %r0
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	rldicl %r4, %r3, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r3, %r4, %r3
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	stw %r9, 4(%r5)
	li %r5, 12
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
	li %r11, 14
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r11, 24(%r11)
	li %r12, 14
	mulld %r12, %r12, %r30
	add %r12, %r12, %r31
	addi %r12, %r12, 160
	ld %r12, 32(%r12)
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	li %r9, 0
264:
	lwz %r0, 0(%r6)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 264b
	lwz %r0, 0(%r6)
	rldicl %r4, %r0, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r0, %r4, %r0
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r7)
	rldicl %r4, %r3, 33, 31
	rldicr %r4, %r4, 32, 31
	subf %r3, %r4, %r3
	mulld %r3, %r12, %r3
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	rldicl %r3, %r0, 1, 63
	rldicr %r3, %r3, 32, 31
	subf %r9, %r3, %r9
	stw %r9, 4(%r5)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r3, 14
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r3, 40(%r3)
	lwz %r0, 0(%r5)
	mulld %r11, %r0, %r3
	rlwinm %r11, %r11, 0, 0, 31
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
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
	li %r9, 0
265:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 265b
	lwz %r0, 0(%r5)
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r6, %r6, 4
	li %r11, 1
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
266:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 266b
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
	li %r5, 13
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
	li %r0, 0
	subf %r9, %r9, %r0
268:
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
	bne %cr0, 268b
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
	li %r9, 0
269:
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
	bne %cr0, 269b
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
	li %r0, 0
	subf %r9, %r9, %r0
270:
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
	bne %cr0, 270b
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r3, 14
	mulld %r3, %r3, %r30
	add %r3, %r3, %r31
	addi %r3, %r3, 160
	ld %r3, 40(%r3)
	lwz %r0, 0(%r5)
	mulld %r11, %r0, %r3
	rlwinm %r11, %r11, 0, 0, 31
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
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
	li %r9, 0
271:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 271b
	lwz %r0, 0(%r5)
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 2
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	addi %r6, %r6, 4
	li %r11, 1
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	addi %r8, %r8, 1
	li %r9, 0
272:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 272b
	li %r5, 12
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
	li %r9, 0
273:
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
	bne %cr0, 273b
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
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
	li %r0, 0
	subf %r9, %r9, %r0
274:
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
	bne %cr0, 274b
	li %r5, 12
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
	li %r9, 0
275:
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
	bne %cr0, 275b
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 12
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
	li %r0, 0
	subf %r9, %r9, %r0
276:
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
	bne %cr0, 276b
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 258b
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
	li %r9, 0
277:
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
	bne %cr0, 277b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	rldicr %r8, %r8, 2, 61
	add %r6, %r6, %r8
	lwz %r9, 0(%r6)
	rldicl %r9, %r9, 33, 31
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
278:
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
	bne %cr0, 278b
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
	li %r9, 0
279:
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
	bne %cr0, 279b
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
	li %r0, 0
	subf %r9, %r9, %r0
280:
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
	bne %cr0, 280b
	addi %r3, %r10, 1
	add %r0, %r3, %r3
	add %r3, %r3, %r0
	add %r3, %r3, %r3
	rldicr %r3, %r3, 15, 48
	add %r10, %r10, %r3
281:
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
	li %r9, 0
282:
	lwz %r0, 0(%r7)
	mulld %r0, %r11, %r0
	lwz %r3, 0(%r6)
	add %r0, %r0, %r3
	add %r0, %r0, %r9
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 32, 32
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 282b
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
	li %r9, 0
283:
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
	bne %cr0, 283b
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
	li %r0, 0
	subf %r9, %r9, %r0
284:
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
	bne %cr0, 284b
	addi %r10, %r10, -32768
	rldicl %r3, %r10, 49, 15
	cmpldi %cr0, %r3, 0
	bne %cr0, 281b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
285:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 285b
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
	li %r9, 0
286:
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
	bne %cr0, 286b
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	rldicr %r8, %r10, 49, 14
	rldicl %r8, %r8, 15, 49
	rldicr %r8, %r8, 2, 61
	add %r6, %r6, %r8
	lwz %r9, 0(%r6)
	rldicl %r9, %r9, 33, 31
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
287:
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
	bne %cr0, 287b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
288:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 288b
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
289:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 289b
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
	beq %cr0, 290f
	addi %r8, %r29, 0
292:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 292b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 148(%r31)
	b 291f
290:
	rldicl %r8, %r29, 63, 1
293:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 293b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 148(%r31)
291:
	lwz %r0, 136(%r31)
	lwz %r3, 140(%r31)
	and %r0, %r0, %r3
	stw %r0, 152(%r31)
	lwz %r0, 152(%r31)
	lwz %r3, 144(%r31)
	and %r0, %r0, %r3
	stw %r0, 152(%r31)
	lwz %r0, 152(%r31)
	lwz %r3, 148(%r31)
	and %r0, %r0, %r3
	stw %r0, 152(%r31)
	li %r5, 18
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
	beq %cr0, 294f
	addi %r8, %r29, 0
296:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 296b
	b 295f
294:
	rldicl %r8, %r29, 63, 1
297:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 297b
295:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
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
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2102:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2102b
	rldicr %r4, %r29, 5, 58
2103:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2104f
	addi %r8, %r29, 0
2106:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2106b
	b 2105f
2104:
	rldicl %r8, %r29, 63, 1
2107:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2107b
2105:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2108f
	addi %r8, %r29, 1
2110:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2110b
	b 2109f
2108:
	rldicl %r8, %r29, 63, 1
2111:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2111b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2109:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
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
	beq %cr0, 2112f
	addi %r8, %r29, 1
	li %r9, 0
2114:
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
	bne %cr0, 2114b
	b 2113f
2112:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2115:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2115b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2113:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2116f
	addi %r8, %r29, 1
2118:
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
	bne %cr0, 2118b
	b 2117f
2116:
	rldicl %r8, %r29, 63, 1
2119:
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
	bne %cr0, 2119b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2117:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2103b
	li %r5, 18
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
	beq %cr0, 2120f
	addi %r8, %r29, 0
2122:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2122b
	b 2121f
2120:
	rldicl %r8, %r29, 63, 1
2123:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2123b
2121:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 16
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2124f
	addi %r8, %r29, 0
2126:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2126b
	b 2125f
2124:
	rldicl %r8, %r29, 63, 1
2127:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2127b
2125:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2128:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2128b
	rldicr %r4, %r29, 5, 58
2129:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2130f
	addi %r8, %r29, 0
2132:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2132b
	b 2131f
2130:
	rldicl %r8, %r29, 63, 1
2133:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2133b
2131:
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2134f
	addi %r8, %r29, 1
2136:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2136b
	b 2135f
2134:
	rldicl %r8, %r29, 63, 1
2137:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2137b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2135:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 23
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
	beq %cr0, 2138f
	addi %r8, %r29, 1
	li %r9, 0
2140:
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
	bne %cr0, 2140b
	b 2139f
2138:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2141:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2141b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2139:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 23
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2142f
	addi %r8, %r29, 1
2144:
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
	bne %cr0, 2144b
	b 2143f
2142:
	rldicl %r8, %r29, 63, 1
2145:
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
	bne %cr0, 2145b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2143:
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2129b
	addi %r5, %r14, 0
	addi %r8, %r20, 0
	lwz %r9, 152(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2146:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2146b
	addi %r5, %r15, 0
	addi %r8, %r22, 0
	lwz %r9, 152(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 23
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2147:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2147b
	addi %r5, %r16, 0
	addi %r8, %r20, 0
	lwz %r9, 152(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 3
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2148:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2148b
	lwz %r3, 152(%r31)
25:
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

vg_rsa_check_key:
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
	std %r26, 88(%r11)
	std %r29, 96(%r11)
	std %r30, 104(%r11)
	std %r31, 112(%r11)
	addi %r31, %r11, 0
	addi %r14, %r3, 0
	addi %r15, %r4, 0
	addi %r16, %r7, 0
	addi %r17, %r8, 0
	addi %r18, %r9, 0
	addi %r19, %r10, 0
	addi %r7, %r5, 0
	addi %r8, %r6, 0
	li %r24, 0
20:
	lbz %r0, 0(%r7)
	rldicr %r24, %r24, 8, 55
	or %r24, %r24, %r0
	rldicl %r3, %r24, 31, 33
	li %r4, 0
	subf %r3, %r3, %r4
	rldicl %r3, %r3, 1, 63
	subf %r3, %r3, %r4
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	xor %r0, %r24, %r4
	and %r0, %r0, %r3
	xor %r24, %r24, %r0
	addi %r7, %r7, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	li %r4, 1
	and %r0, %r24, %r4
	addi %r3, %r24, -3
	rldicl %r3, %r3, 1, 63
	xor %r3, %r3, %r4
	and %r0, %r0, %r3
	rldicr %r3, %r4, 33, 30
	subf %r3, %r3, %r24
	rldicl %r3, %r3, 1, 63
	and %r0, %r0, %r3
	li %r3, 0
	subf %r26, %r0, %r3
	rldicr %r24, %r24, 31, 32
	cmpldi %cr0, %r26, 0
	beq %cr0, 21f
	addi %r20, %r1, 96
	ld %r20, 0(%r20)
	addi %r21, %r1, 104
	ld %r21, 0(%r21)
	addi %r22, %r1, 112
	ld %r22, 0(%r22)
	addi %r23, %r1, 128
	ld %r23, 0(%r23)
	addi %r26, %r1, 144
	ld %r26, 0(%r26)
	addi %r9, %r14, 0
	addi %r10, %r15, 0
	add %r11, %r9, %r10
	addi %r11, %r11, -1
	lbz %r0, 0(%r11)
	li %r12, 1
	and %r0, %r0, %r12
	xor %r0, %r0, %r12
	lbz %r11, 0(%r9)
	cmpldi %cr0, %r11, 0
	beq %cr0, 23f
	b 24f
23:
	li %r0, 1
24:
	addi %r12, %r10, -64
	cmpldi %cr0, %r12, 0
	beq %cr0, 25f
	b 26f
25:
	rldicl %r11, %r11, 57, 7
	li %r12, 1
	xor %r11, %r11, %r12
	or %r0, %r0, %r11
26:
	cmpldi %cr0, %r0, 0
	beq %cr0, 27f
	li %r3, 0
	b 28f
27:
	addi %r29, %r15, 3
	rldicl %r29, %r29, 62, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r8, 24
	mulld %r8, %r8, %r30
	rldicl %r8, %r8, 62, 2
	addi %r5, %r31, 160
	li %r0, 0
29:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 29b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicl %r0, %r24, 33, 31
	stw %r0, 0(%r5)
	rldicl %r0, %r0, 32, 32
	stw %r0, 4(%r5)
	addi %r6, %r14, 0
	addi %r8, %r15, 0
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
210:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 210b
	addi %r6, %r16, 0
	addi %r8, %r17, 0
	li %r5, 9
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
211:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 211b
	addi %r6, %r18, 0
	addi %r8, %r19, 0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
212:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 212b
	addi %r6, %r20, 0
	addi %r8, %r21, 0
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
213:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 213b
	addi %r6, %r22, 0
	addi %r8, %r19, 0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
214:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 214b
	addi %r6, %r23, 0
	addi %r8, %r21, 0
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
215:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 215b
	addi %r6, %r26, 0
	addi %r8, %r19, 0
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
216:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 216b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 217f
	addi %r8, %r29, 0
219:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 219b
	b 218f
217:
	rldicl %r8, %r29, 63, 1
220:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 220b
218:
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 221f
	addi %r8, %r29, 0
223:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 223b
	b 222f
221:
	rldicl %r8, %r29, 63, 1
224:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 224b
222:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
225:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 225b
	rldicr %r4, %r29, 5, 58
226:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 227f
	addi %r8, %r29, 0
229:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 229b
	b 228f
227:
	rldicl %r8, %r29, 63, 1
230:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 230b
228:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 231f
	addi %r8, %r29, 1
233:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 233b
	b 232f
231:
	rldicl %r8, %r29, 63, 1
234:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 234b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
232:
	li %r5, 15
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
	beq %cr0, 235f
	addi %r8, %r29, 1
	li %r9, 0
237:
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
	bne %cr0, 237b
	b 236f
235:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
238:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 238b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
236:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
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
	beq %cr0, 239f
	addi %r8, %r29, 1
241:
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
	bne %cr0, 241b
	b 240f
239:
	rldicl %r8, %r29, 63, 1
242:
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
	bne %cr0, 242b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
240:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 226b
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 5
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 243f
	addi %r8, %r29, 0
245:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 245b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 244f
243:
	rldicl %r8, %r29, 63, 1
246:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 246b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
244:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 0
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 247f
	addi %r8, %r29, 0
249:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 249b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 248f
247:
	rldicl %r8, %r29, 63, 1
250:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 250b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
248:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 251f
	addi %r8, %r29, 0
253:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 253b
	b 252f
251:
	rldicl %r8, %r29, 63, 1
254:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 254b
252:
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 255f
	addi %r8, %r29, 0
257:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 257b
	b 256f
255:
	rldicl %r8, %r29, 63, 1
258:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 258b
256:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
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
	beq %cr0, 259f
	addi %r8, %r29, 0
	li %r9, 0
261:
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
	bne %cr0, 261b
	b 260f
259:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
262:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 262b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
260:
	stw %r9, 136(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 16
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
	beq %cr0, 263f
	addi %r8, %r29, 0
265:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 265b
	b 264f
263:
	rldicl %r8, %r29, 63, 1
266:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 266b
264:
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 267f
	addi %r8, %r29, 0
269:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 269b
	b 268f
267:
	rldicl %r8, %r29, 63, 1
270:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 270b
268:
	li %r5, 18
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
	beq %cr0, 271f
	addi %r8, %r29, 0
273:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 273b
	b 272f
271:
	rldicl %r8, %r29, 63, 1
274:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 274b
272:
	li %r4, 33
275:
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 276f
	addi %r8, %r29, 0
278:
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
	bne %cr0, 278b
	b 277f
276:
	rldicl %r8, %r29, 63, 1
279:
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
	bne %cr0, 279b
277:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 280f
	addi %r8, %r29, 0
	li %r9, 0
282:
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
	bne %cr0, 282b
	b 281f
280:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
283:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 283b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
281:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
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
	beq %cr0, 284f
	addi %r8, %r29, 0
	li %r9, 0
286:
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
	bne %cr0, 286b
	b 285f
284:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
287:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 287b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
285:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
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
	beq %cr0, 288f
	addi %r8, %r29, 0
	li %r9, 0
290:
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
	bne %cr0, 290b
	b 289f
288:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
291:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 291b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
289:
	stw %r9, 132(%r31)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 292f
	addi %r8, %r29, 0
294:
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
	bne %cr0, 294b
	b 293f
292:
	rldicl %r8, %r29, 63, 1
295:
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
	bne %cr0, 295b
293:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 296f
	addi %r8, %r29, 0
	li %r9, 0
298:
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
	bne %cr0, 298b
	b 297f
296:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
299:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 299b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
297:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
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
	beq %cr0, 2100f
	addi %r8, %r29, 0
	li %r9, 0
2102:
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
	bne %cr0, 2102b
	b 2101f
2100:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2103:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2103b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2101:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
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
	beq %cr0, 2104f
	addi %r8, %r29, 0
	li %r9, 0
2106:
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
	bne %cr0, 2106b
	b 2105f
2104:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2107:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2107b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2105:
	stw %r9, 132(%r31)
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2108f
	addi %r8, %r29, 0
2110:
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
	bne %cr0, 2110b
	b 2109f
2108:
	rldicl %r8, %r29, 63, 1
2111:
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
	bne %cr0, 2111b
2109:
	li %r9, 0
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2112f
	addi %r8, %r29, 0
2114:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2114b
	b 2113f
2112:
	rldicl %r8, %r29, 63, 1
2115:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2115b
2113:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 275b
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2116f
	addi %r8, %r29, 0
2118:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2118b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 2117f
2116:
	rldicl %r8, %r29, 63, 1
2119:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2119b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
2117:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2120f
	addi %r8, %r29, 0
	li %r9, 0
2122:
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
	bne %cr0, 2122b
	b 2121f
2120:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2123:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2123b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2121:
	stw %r9, 136(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 16
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
	beq %cr0, 2124f
	addi %r8, %r29, 0
2126:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2126b
	b 2125f
2124:
	rldicl %r8, %r29, 63, 1
2127:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2127b
2125:
	li %r5, 17
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
	beq %cr0, 2128f
	addi %r8, %r29, 0
2130:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2130b
	b 2129f
2128:
	rldicl %r8, %r29, 63, 1
2131:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2131b
2129:
	li %r5, 18
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
	beq %cr0, 2132f
	addi %r8, %r29, 0
2134:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2134b
	b 2133f
2132:
	rldicl %r8, %r29, 63, 1
2135:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2135b
2133:
	li %r4, 33
2136:
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2137f
	addi %r8, %r29, 0
2139:
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
	bne %cr0, 2139b
	b 2138f
2137:
	rldicl %r8, %r29, 63, 1
2140:
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
	bne %cr0, 2140b
2138:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 2141f
	addi %r8, %r29, 0
	li %r9, 0
2143:
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
	bne %cr0, 2143b
	b 2142f
2141:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2144:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2144b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2142:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
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
	beq %cr0, 2145f
	addi %r8, %r29, 0
	li %r9, 0
2147:
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
	bne %cr0, 2147b
	b 2146f
2145:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2148:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2148b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2146:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2149f
	addi %r8, %r29, 0
	li %r9, 0
2151:
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
	bne %cr0, 2151b
	b 2150f
2149:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2152:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2152b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2150:
	stw %r9, 132(%r31)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2153f
	addi %r8, %r29, 0
2155:
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
	bne %cr0, 2155b
	b 2154f
2153:
	rldicl %r8, %r29, 63, 1
2156:
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
	bne %cr0, 2156b
2154:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 2157f
	addi %r8, %r29, 0
	li %r9, 0
2159:
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
	bne %cr0, 2159b
	b 2158f
2157:
	rldicl %r8, %r29, 63, 1
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
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2158:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
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
	beq %cr0, 2161f
	addi %r8, %r29, 0
	li %r9, 0
2163:
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
	bne %cr0, 2163b
	b 2162f
2161:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2164:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2164b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2162:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2165f
	addi %r8, %r29, 0
	li %r9, 0
2167:
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
	bne %cr0, 2167b
	b 2166f
2165:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2168:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2168b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2166:
	stw %r9, 132(%r31)
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2169f
	addi %r8, %r29, 0
2171:
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
	bne %cr0, 2171b
	b 2170f
2169:
	rldicl %r8, %r29, 63, 1
2172:
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
	bne %cr0, 2172b
2170:
	li %r9, 0
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2173f
	addi %r8, %r29, 0
2175:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2175b
	b 2174f
2173:
	rldicl %r8, %r29, 63, 1
2176:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2176b
2174:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2136b
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2177f
	addi %r8, %r29, 0
2179:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2179b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 2178f
2177:
	rldicl %r8, %r29, 63, 1
2180:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2180b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
2178:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
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
	beq %cr0, 2181f
	addi %r8, %r29, 0
	li %r9, 0
2183:
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
	bne %cr0, 2183b
	b 2182f
2181:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2184:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2184b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2182:
	stw %r9, 136(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2185f
	addi %r8, %r29, 0
2187:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2187b
	b 2186f
2185:
	rldicl %r8, %r29, 63, 1
2188:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2188b
2186:
	li %r5, 17
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
	beq %cr0, 2189f
	addi %r8, %r29, 0
2191:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2191b
	b 2190f
2189:
	rldicl %r8, %r29, 63, 1
2192:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2192b
2190:
	li %r5, 18
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
	beq %cr0, 2193f
	addi %r8, %r29, 0
2195:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2195b
	b 2194f
2193:
	rldicl %r8, %r29, 63, 1
2196:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2196b
2194:
	rldicr %r4, %r21, 3, 60
2197:
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2198f
	addi %r8, %r29, 0
2200:
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
	bne %cr0, 2200b
	b 2199f
2198:
	rldicl %r8, %r29, 63, 1
2201:
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
	bne %cr0, 2201b
2199:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 2202f
	addi %r8, %r29, 0
	li %r9, 0
2204:
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
	bne %cr0, 2204b
	b 2203f
2202:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2205:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2205b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2203:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
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
	beq %cr0, 2206f
	addi %r8, %r29, 0
	li %r9, 0
2208:
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
	bne %cr0, 2208b
	b 2207f
2206:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2209:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2209b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2207:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
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
	beq %cr0, 2210f
	addi %r8, %r29, 0
	li %r9, 0
2212:
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
	bne %cr0, 2212b
	b 2211f
2210:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2213:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2213b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2211:
	stw %r9, 132(%r31)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2214f
	addi %r8, %r29, 0
2216:
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
	bne %cr0, 2216b
	b 2215f
2214:
	rldicl %r8, %r29, 63, 1
2217:
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
	bne %cr0, 2217b
2215:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 2218f
	addi %r8, %r29, 0
	li %r9, 0
2220:
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
	bne %cr0, 2220b
	b 2219f
2218:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2221:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2221b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2219:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
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
	beq %cr0, 2222f
	addi %r8, %r29, 0
	li %r9, 0
2224:
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
	bne %cr0, 2224b
	b 2223f
2222:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2225:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2225b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2223:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
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
	beq %cr0, 2226f
	addi %r8, %r29, 0
	li %r9, 0
2228:
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
	bne %cr0, 2228b
	b 2227f
2226:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2229:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2229b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2227:
	stw %r9, 132(%r31)
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2230f
	addi %r8, %r29, 0
2232:
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
	bne %cr0, 2232b
	b 2231f
2230:
	rldicl %r8, %r29, 63, 1
2233:
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
	bne %cr0, 2233b
2231:
	li %r9, 0
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2234f
	addi %r8, %r29, 0
2236:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2236b
	b 2235f
2234:
	rldicl %r8, %r29, 63, 1
2237:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2237b
2235:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2197b
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2238f
	addi %r8, %r29, 0
2240:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2240b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 2239f
2238:
	rldicl %r8, %r29, 63, 1
2241:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2241b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
2239:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 9
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
	beq %cr0, 2242f
	addi %r8, %r29, 0
	li %r9, 0
2244:
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
	bne %cr0, 2244b
	b 2243f
2242:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2245:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2245b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2243:
	stw %r9, 136(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 9
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2246f
	addi %r8, %r29, 0
2248:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2248b
	b 2247f
2246:
	rldicl %r8, %r29, 63, 1
2249:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2249b
2247:
	li %r5, 14
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
	beq %cr0, 2250f
	addi %r8, %r29, 0
2252:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2252b
	b 2251f
2250:
	rldicl %r8, %r29, 63, 1
2253:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2253b
2251:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2254:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2254b
	rldicr %r4, %r29, 5, 58
2255:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2256f
	addi %r8, %r29, 0
2258:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2258b
	b 2257f
2256:
	rldicl %r8, %r29, 63, 1
2259:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2259b
2257:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2260f
	addi %r8, %r29, 1
2262:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2262b
	b 2261f
2260:
	rldicl %r8, %r29, 63, 1
2263:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2263b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2261:
	li %r5, 15
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
	beq %cr0, 2264f
	addi %r8, %r29, 1
	li %r9, 0
2266:
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
	bne %cr0, 2266b
	b 2265f
2264:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2267:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2267b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2265:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
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
	beq %cr0, 2268f
	addi %r8, %r29, 1
2270:
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
	bne %cr0, 2270b
	b 2269f
2268:
	rldicl %r8, %r29, 63, 1
2271:
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
	bne %cr0, 2271b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2269:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2255b
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 6
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2272f
	addi %r8, %r29, 0
2274:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2274b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 2273f
2272:
	rldicl %r8, %r29, 63, 1
2275:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2275b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
2273:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 9
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2276f
	addi %r8, %r29, 0
2278:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2278b
	b 2277f
2276:
	rldicl %r8, %r29, 63, 1
2279:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2279b
2277:
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 11
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2280f
	addi %r8, %r29, 0
2282:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2282b
	b 2281f
2280:
	rldicl %r8, %r29, 63, 1
2283:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2283b
2281:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2284:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2284b
	rldicr %r4, %r29, 5, 58
2285:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2286f
	addi %r8, %r29, 0
2288:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2288b
	b 2287f
2286:
	rldicl %r8, %r29, 63, 1
2289:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2289b
2287:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2290f
	addi %r8, %r29, 1
2292:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2292b
	b 2291f
2290:
	rldicl %r8, %r29, 63, 1
2293:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2293b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2291:
	li %r5, 15
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
	beq %cr0, 2294f
	addi %r8, %r29, 1
	li %r9, 0
2296:
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
	bne %cr0, 2296b
	b 2295f
2294:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2297:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2297b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2295:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
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
	beq %cr0, 2298f
	addi %r8, %r29, 1
2300:
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
	bne %cr0, 2300b
	b 2299f
2298:
	rldicl %r8, %r29, 63, 1
2301:
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
	bne %cr0, 2301b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2299:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2285b
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2302f
	addi %r8, %r29, 0
2304:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2304b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 2303f
2302:
	rldicl %r8, %r29, 63, 1
2305:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2305b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
2303:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	lwz %r3, 140(%r31)
28:
	b 22f
21:
	li %r3, 0
22:
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
	ld %r26, 88(%r31)
	ld %r29, 96(%r31)
	ld %r30, 104(%r31)
	ld %r31, 112(%r31)
	blr

vg_rsa_check_crt_key:
	addi %r11, %r1, 144
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
	std %r26, 88(%r11)
	std %r29, 96(%r11)
	std %r30, 104(%r11)
	std %r31, 112(%r11)
	addi %r31, %r11, 0
	addi %r14, %r3, 0
	addi %r15, %r4, 0
	addi %r18, %r7, 0
	addi %r19, %r8, 0
	addi %r20, %r9, 0
	addi %r21, %r10, 0
	addi %r7, %r5, 0
	addi %r8, %r6, 0
	li %r24, 0
20:
	lbz %r0, 0(%r7)
	rldicr %r24, %r24, 8, 55
	or %r24, %r24, %r0
	rldicl %r3, %r24, 31, 33
	li %r4, 0
	subf %r3, %r3, %r4
	rldicl %r3, %r3, 1, 63
	subf %r3, %r3, %r4
	li %r4, 1
	rldicr %r4, %r4, 33, 30
	xor %r0, %r24, %r4
	and %r0, %r0, %r3
	xor %r24, %r24, %r0
	addi %r7, %r7, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 20b
	li %r4, 1
	and %r0, %r24, %r4
	addi %r3, %r24, -3
	rldicl %r3, %r3, 1, 63
	xor %r3, %r3, %r4
	and %r0, %r0, %r3
	rldicr %r3, %r4, 33, 30
	subf %r3, %r3, %r24
	rldicl %r3, %r3, 1, 63
	and %r0, %r0, %r3
	li %r3, 0
	subf %r26, %r0, %r3
	rldicr %r24, %r24, 31, 32
	cmpldi %cr0, %r26, 0
	beq %cr0, 21f
	addi %r22, %r1, 96
	ld %r22, 0(%r22)
	addi %r23, %r1, 112
	ld %r23, 0(%r23)
	addi %r26, %r1, 128
	ld %r26, 0(%r26)
	addi %r9, %r14, 0
	addi %r10, %r15, 0
	add %r11, %r9, %r10
	addi %r11, %r11, -1
	lbz %r0, 0(%r11)
	li %r12, 1
	and %r0, %r0, %r12
	xor %r0, %r0, %r12
	lbz %r11, 0(%r9)
	cmpldi %cr0, %r11, 0
	beq %cr0, 23f
	b 24f
23:
	li %r0, 1
24:
	addi %r12, %r10, -64
	cmpldi %cr0, %r12, 0
	beq %cr0, 25f
	b 26f
25:
	rldicl %r11, %r11, 57, 7
	li %r12, 1
	xor %r11, %r11, %r12
	or %r0, %r0, %r11
26:
	cmpldi %cr0, %r0, 0
	beq %cr0, 27f
	li %r3, 0
	b 28f
27:
	addi %r29, %r15, 3
	rldicl %r29, %r29, 62, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	li %r8, 24
	mulld %r8, %r8, %r30
	rldicl %r8, %r8, 62, 2
	addi %r5, %r31, 160
	li %r0, 0
29:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 29b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicl %r0, %r24, 33, 31
	stw %r0, 0(%r5)
	rldicl %r0, %r0, 32, 32
	stw %r0, 4(%r5)
	addi %r6, %r14, 0
	addi %r8, %r15, 0
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
210:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 210b
	addi %r6, %r18, 0
	addi %r8, %r19, 0
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
211:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 211b
	addi %r6, %r20, 0
	addi %r8, %r21, 0
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
212:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 212b
	addi %r6, %r22, 0
	addi %r8, %r19, 0
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
213:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 213b
	addi %r6, %r23, 0
	addi %r8, %r21, 0
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
214:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 214b
	addi %r6, %r26, 0
	addi %r8, %r19, 0
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
215:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 215b
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 2
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 216f
	addi %r8, %r29, 0
218:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 218b
	b 217f
216:
	rldicl %r8, %r29, 63, 1
219:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 219b
217:
	li %r5, 14
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 220f
	addi %r8, %r29, 0
222:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 222b
	b 221f
220:
	rldicl %r8, %r29, 63, 1
223:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 223b
221:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
224:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 224b
	rldicr %r4, %r29, 5, 58
225:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 226f
	addi %r8, %r29, 0
228:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 228b
	b 227f
226:
	rldicl %r8, %r29, 63, 1
229:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 229b
227:
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 230f
	addi %r8, %r29, 1
232:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 232b
	b 231f
230:
	rldicl %r8, %r29, 63, 1
233:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 233b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
231:
	li %r5, 15
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
	beq %cr0, 234f
	addi %r8, %r29, 1
	li %r9, 0
236:
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
	bne %cr0, 236b
	b 235f
234:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
237:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 237b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
235:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 13
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 13
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
	beq %cr0, 238f
	addi %r8, %r29, 1
240:
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
	bne %cr0, 240b
	b 239f
238:
	rldicl %r8, %r29, 63, 1
241:
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
	bne %cr0, 241b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
239:
	li %r5, 12
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 225b
	li %r6, 12
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 5
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 242f
	addi %r8, %r29, 0
244:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 244b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 243f
242:
	rldicl %r8, %r29, 63, 1
245:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 245b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
243:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r6, 13
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 0
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 246f
	addi %r8, %r29, 0
248:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 248b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 247f
246:
	rldicl %r8, %r29, 63, 1
249:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 249b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
247:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 4
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 250f
	addi %r8, %r29, 0
252:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 252b
	b 251f
250:
	rldicl %r8, %r29, 63, 1
253:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 253b
251:
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 254f
	addi %r8, %r29, 0
256:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 256b
	b 255f
254:
	rldicl %r8, %r29, 63, 1
257:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 257b
255:
	li %r5, 11
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
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
	beq %cr0, 258f
	addi %r8, %r29, 0
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
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
259:
	stw %r9, 136(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 16
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
	beq %cr0, 262f
	addi %r8, %r29, 0
264:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 264b
	b 263f
262:
	rldicl %r8, %r29, 63, 1
265:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 265b
263:
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 266f
	addi %r8, %r29, 0
268:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 268b
	b 267f
266:
	rldicl %r8, %r29, 63, 1
269:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 269b
267:
	li %r5, 18
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
	beq %cr0, 270f
	addi %r8, %r29, 0
272:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 272b
	b 271f
270:
	rldicl %r8, %r29, 63, 1
273:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 273b
271:
	li %r4, 33
274:
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 275f
	addi %r8, %r29, 0
277:
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
	bne %cr0, 277b
	b 276f
275:
	rldicl %r8, %r29, 63, 1
278:
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
	bne %cr0, 278b
276:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 279f
	addi %r8, %r29, 0
	li %r9, 0
281:
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
	bne %cr0, 281b
	b 280f
279:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
282:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 282b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
280:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
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
	beq %cr0, 283f
	addi %r8, %r29, 0
	li %r9, 0
285:
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
	bne %cr0, 285b
	b 284f
283:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
286:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 286b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
284:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
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
	beq %cr0, 287f
	addi %r8, %r29, 0
	li %r9, 0
289:
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
	bne %cr0, 289b
	b 288f
287:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
290:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 290b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
288:
	stw %r9, 132(%r31)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 291f
	addi %r8, %r29, 0
293:
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
	bne %cr0, 293b
	b 292f
291:
	rldicl %r8, %r29, 63, 1
294:
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
	bne %cr0, 294b
292:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 295f
	addi %r8, %r29, 0
	li %r9, 0
297:
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
	bne %cr0, 297b
	b 296f
295:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
298:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 298b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
296:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
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
	beq %cr0, 299f
	addi %r8, %r29, 0
	li %r9, 0
2101:
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
	bne %cr0, 2101b
	b 2100f
299:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2102:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2102b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2100:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
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
	beq %cr0, 2103f
	addi %r8, %r29, 0
	li %r9, 0
2105:
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
	bne %cr0, 2105b
	b 2104f
2103:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2106:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2106b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2104:
	stw %r9, 132(%r31)
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2107f
	addi %r8, %r29, 0
2109:
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
	bne %cr0, 2109b
	b 2108f
2107:
	rldicl %r8, %r29, 63, 1
2110:
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
	bne %cr0, 2110b
2108:
	li %r9, 0
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2111f
	addi %r8, %r29, 0
2113:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2113b
	b 2112f
2111:
	rldicl %r8, %r29, 63, 1
2114:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2114b
2112:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 274b
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2115f
	addi %r8, %r29, 0
2117:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2117b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 2116f
2115:
	rldicl %r8, %r29, 63, 1
2118:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2118b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
2116:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2119f
	addi %r8, %r29, 0
	li %r9, 0
2121:
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
	bne %cr0, 2121b
	b 2120f
2119:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2122:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2122b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2120:
	stw %r9, 136(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 16
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
	beq %cr0, 2123f
	addi %r8, %r29, 0
2125:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2125b
	b 2124f
2123:
	rldicl %r8, %r29, 63, 1
2126:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2126b
2124:
	li %r5, 17
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
	beq %cr0, 2127f
	addi %r8, %r29, 0
2129:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2129b
	b 2128f
2127:
	rldicl %r8, %r29, 63, 1
2130:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2130b
2128:
	li %r5, 18
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
	beq %cr0, 2131f
	addi %r8, %r29, 0
2133:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2133b
	b 2132f
2131:
	rldicl %r8, %r29, 63, 1
2134:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2134b
2132:
	li %r4, 33
2135:
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2136f
	addi %r8, %r29, 0
2138:
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
	bne %cr0, 2138b
	b 2137f
2136:
	rldicl %r8, %r29, 63, 1
2139:
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
	bne %cr0, 2139b
2137:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 2140f
	addi %r8, %r29, 0
	li %r9, 0
2142:
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
	bne %cr0, 2142b
	b 2141f
2140:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2143:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2143b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2141:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
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
	beq %cr0, 2144f
	addi %r8, %r29, 0
	li %r9, 0
2146:
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
	bne %cr0, 2146b
	b 2145f
2144:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2147:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2147b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2145:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2148f
	addi %r8, %r29, 0
	li %r9, 0
2150:
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
	bne %cr0, 2150b
	b 2149f
2148:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2151:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2151b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2149:
	stw %r9, 132(%r31)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2152f
	addi %r8, %r29, 0
2154:
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
	bne %cr0, 2154b
	b 2153f
2152:
	rldicl %r8, %r29, 63, 1
2155:
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
	bne %cr0, 2155b
2153:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 2156f
	addi %r8, %r29, 0
	li %r9, 0
2158:
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
	bne %cr0, 2158b
	b 2157f
2156:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2159:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2159b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2157:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
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
	beq %cr0, 2160f
	addi %r8, %r29, 0
	li %r9, 0
2162:
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
	bne %cr0, 2162b
	b 2161f
2160:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2163:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2163b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2161:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 11
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2164f
	addi %r8, %r29, 0
	li %r9, 0
2166:
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
	bne %cr0, 2166b
	b 2165f
2164:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2167:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2167b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2165:
	stw %r9, 132(%r31)
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2168f
	addi %r8, %r29, 0
2170:
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
	bne %cr0, 2170b
	b 2169f
2168:
	rldicl %r8, %r29, 63, 1
2171:
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
	bne %cr0, 2171b
2169:
	li %r9, 0
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2172f
	addi %r8, %r29, 0
2174:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2174b
	b 2173f
2172:
	rldicl %r8, %r29, 63, 1
2175:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2175b
2173:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2135b
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2176f
	addi %r8, %r29, 0
2178:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2178b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 2177f
2176:
	rldicl %r8, %r29, 63, 1
2179:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2179b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
2177:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 23
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
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
	beq %cr0, 2180f
	addi %r8, %r29, 0
	li %r9, 0
2182:
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
	bne %cr0, 2182b
	b 2181f
2180:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2183:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2183b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2181:
	stw %r9, 136(%r31)
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2184f
	addi %r8, %r29, 0
2186:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2186b
	b 2185f
2184:
	rldicl %r8, %r29, 63, 1
2187:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2187b
2185:
	li %r5, 17
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
	beq %cr0, 2188f
	addi %r8, %r29, 0
2190:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2190b
	b 2189f
2188:
	rldicl %r8, %r29, 63, 1
2191:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2191b
2189:
	li %r5, 18
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
	beq %cr0, 2192f
	addi %r8, %r29, 0
2194:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2194b
	b 2193f
2192:
	rldicl %r8, %r29, 63, 1
2195:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2195b
2193:
	rldicr %r4, %r21, 3, 60
2196:
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
	li %r5, 19
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 17
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2197f
	addi %r8, %r29, 0
2199:
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
	bne %cr0, 2199b
	b 2198f
2197:
	rldicl %r8, %r29, 63, 1
2200:
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
	bne %cr0, 2200b
2198:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 2201f
	addi %r8, %r29, 0
	li %r9, 0
2203:
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
	bne %cr0, 2203b
	b 2202f
2201:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2204:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2204b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2202:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 18
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
	beq %cr0, 2205f
	addi %r8, %r29, 0
	li %r9, 0
2207:
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
	bne %cr0, 2207b
	b 2206f
2205:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2208:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2208b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2206:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
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
	beq %cr0, 2209f
	addi %r8, %r29, 0
	li %r9, 0
2211:
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
	bne %cr0, 2211b
	b 2210f
2209:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2212:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2212b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2210:
	stw %r9, 132(%r31)
	li %r5, 18
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2213f
	addi %r8, %r29, 0
2215:
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
	bne %cr0, 2215b
	b 2214f
2213:
	rldicl %r8, %r29, 63, 1
2216:
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
	bne %cr0, 2216b
2214:
	li %r5, 20
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 2217f
	addi %r8, %r29, 0
	li %r9, 0
2219:
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
	bne %cr0, 2219b
	b 2218f
2217:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2220:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2220b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2218:
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 17
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
	beq %cr0, 2221f
	addi %r8, %r29, 0
	li %r9, 0
2223:
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
	bne %cr0, 2223b
	b 2222f
2221:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2224:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2224b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2222:
	li %r5, 22
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 21
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
	beq %cr0, 2225f
	addi %r8, %r29, 0
	li %r9, 0
2227:
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
	bne %cr0, 2227b
	b 2226f
2225:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2228:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2228b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2226:
	stw %r9, 132(%r31)
	li %r5, 17
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 22
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 21
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2229f
	addi %r8, %r29, 0
2231:
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
	bne %cr0, 2231b
	b 2230f
2229:
	rldicl %r8, %r29, 63, 1
2232:
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
	bne %cr0, 2232b
2230:
	li %r9, 0
	li %r5, 16
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2233f
	addi %r8, %r29, 0
2235:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2235b
	b 2234f
2233:
	rldicl %r8, %r29, 63, 1
2236:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2236b
2234:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2196b
	li %r6, 18
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2237f
	addi %r8, %r29, 0
2239:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2239b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
	b 2238f
2237:
	rldicl %r8, %r29, 63, 1
2240:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2240b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 136(%r31)
2238:
	lwz %r0, 140(%r31)
	lwz %r3, 136(%r31)
	and %r0, %r0, %r3
	stw %r0, 140(%r31)
	lwz %r3, 140(%r31)
28:
	b 22f
21:
	li %r3, 0
22:
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
	ld %r26, 88(%r31)
	ld %r29, 96(%r31)
	ld %r30, 104(%r31)
	ld %r31, 112(%r31)
	blr

vg_rsa_recover_primes:
	addi %r11, %r1, 112
	ld %r11, 0(%r11)
	addi %r12, %r8, 7
	rldicl %r12, %r12, 61, 3
	rldicr %r12, %r12, 1, 62
	addi %r12, %r12, 2
	addi %r0, %r12, 2
	rldicr %r0, %r0, 2, 61
	li %r12, 44
	mulld %r12, %r12, %r0
	add %r12, %r12, %r11
	addi %r12, %r12, 160
	std %r14, 0(%r12)
	std %r15, 8(%r12)
	std %r16, 16(%r12)
	std %r17, 24(%r12)
	std %r18, 32(%r12)
	std %r19, 40(%r12)
	std %r20, 48(%r12)
	std %r21, 56(%r12)
	std %r22, 64(%r12)
	std %r23, 72(%r12)
	std %r24, 80(%r12)
	std %r25, 88(%r12)
	std %r26, 96(%r12)
	std %r27, 104(%r12)
	std %r28, 112(%r12)
	std %r29, 120(%r12)
	std %r30, 128(%r12)
	std %r31, 136(%r12)
	addi %r31, %r11, 0
	addi %r29, %r8, 7
	rldicl %r29, %r29, 61, 3
	rldicr %r29, %r29, 1, 62
	addi %r29, %r29, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	addi %r21, %r3, 0
	addi %r23, %r5, 0
	addi %r24, %r7, 0
	addi %r25, %r8, 0
	addi %r26, %r9, 0
	addi %r27, %r10, 0
	addi %r28, %r1, 96
	ld %r28, 0(%r28)
	addi %r22, %r1, 104
	ld %r22, 0(%r22)
	addi %r9, %r24, 0
	addi %r10, %r25, 0
	add %r11, %r9, %r10
	addi %r11, %r11, -1
	lbz %r0, 0(%r11)
	li %r12, 1
	and %r0, %r0, %r12
	xor %r0, %r0, %r12
	lbz %r11, 0(%r9)
	cmpldi %cr0, %r11, 0
	beq %cr0, 20f
	b 21f
20:
	li %r0, 1
21:
	addi %r12, %r10, -64
	cmpldi %cr0, %r12, 0
	beq %cr0, 22f
	b 23f
22:
	rldicl %r11, %r11, 57, 7
	li %r12, 1
	xor %r11, %r11, %r12
	or %r0, %r0, %r11
23:
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	addi %r5, %r21, 0
	addi %r8, %r25, 0
	li %r0, 0
26:
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 26b
	addi %r5, %r23, 0
	addi %r8, %r25, 0
	li %r0, 0
27:
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 27b
	li %r3, 0
	b 25f
24:
	li %r8, 44
	mulld %r8, %r8, %r30
	rldicl %r8, %r8, 62, 2
	addi %r5, %r31, 160
	li %r0, 0
28:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 28b
	addi %r6, %r24, 0
	addi %r8, %r25, 0
	li %r5, 32
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
29:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 29b
	rldicr %r29, %r29, 1, 62
	addi %r29, %r29, 2
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	addi %r6, %r26, 0
	addi %r8, %r27, 0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
210:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 210b
	addi %r6, %r28, 0
	addi %r8, %r22, 0
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	add %r5, %r5, %r8
	addi %r5, %r5, -1
211:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r5)
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 211b
	add %r26, %r27, %r22
	rldicr %r26, %r26, 3, 60
	li %r5, 4
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	addi %r5, %r5, -4
	li %r0, 1
	rldicr %r0, %r0, 31, 32
	stw %r0, 0(%r5)
	rldicr %r4, %r27, 3, 60
212:
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 128(%r31)
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
	lwz %r9, 128(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 213f
	addi %r8, %r29, 0
215:
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
	bne %cr0, 215b
	b 214f
213:
	rldicl %r8, %r29, 63, 1
216:
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
	bne %cr0, 216b
214:
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	beq %cr0, 217f
	addi %r8, %r29, 0
	li %r9, 0
219:
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
	bne %cr0, 219b
	b 218f
217:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
220:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 220b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
218:
	li %r5, 7
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 3
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
	beq %cr0, 221f
	addi %r8, %r29, 0
	li %r9, 0
223:
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
	bne %cr0, 223b
	b 222f
221:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
224:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 224b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
222:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
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
	beq %cr0, 225f
	addi %r8, %r29, 0
	li %r9, 0
227:
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
	bne %cr0, 227b
	b 226f
225:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
228:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 228b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
226:
	stw %r9, 132(%r31)
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 229f
	addi %r8, %r29, 0
231:
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
	bne %cr0, 231b
	b 230f
229:
	rldicl %r8, %r29, 63, 1
232:
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
	bne %cr0, 232b
230:
	li %r5, 6
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
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 233f
	addi %r8, %r29, 0
	li %r9, 0
235:
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
	bne %cr0, 235b
	b 234f
233:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
236:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 236b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
234:
	li %r5, 7
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
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 237f
	addi %r8, %r29, 0
	li %r9, 0
239:
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
	bne %cr0, 239b
	b 238f
237:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
240:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 240b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
238:
	li %r5, 8
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 7
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
	beq %cr0, 241f
	addi %r8, %r29, 0
	li %r9, 0
243:
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
	bne %cr0, 243b
	b 242f
241:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
244:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 244b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
242:
	stw %r9, 132(%r31)
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 8
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 7
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 245f
	addi %r8, %r29, 0
247:
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
	bne %cr0, 247b
	b 246f
245:
	rldicl %r8, %r29, 63, 1
248:
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
	bne %cr0, 248b
246:
	li %r9, 0
	li %r5, 1
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r6, %r29, 2, 61
	add %r6, %r5, %r6
	stw %r9, 0(%r6)
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 249f
	addi %r8, %r29, 0
251:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 251b
	b 250f
249:
	rldicl %r8, %r29, 63, 1
252:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 252b
250:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 212b
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	li %r3, 1
	and %r0, %r0, %r3
	stw %r0, 16(%r31)
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	rldicl %r0, %r0, 63, 1
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r5)
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 0
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
	lwz %r0, 16(%r31)
	and %r0, %r0, %r9
	li %r3, 1
	xor %r0, %r0, %r3
	addi %r29, %r29, -2
	rldicl %r29, %r29, 63, 1
	addi %r30, %r29, 2
	rldicr %r30, %r30, 2, 61
	cmpldi %cr0, %r0, 0
	beq %cr0, 257f
	addi %r5, %r21, 0
	addi %r8, %r25, 0
	li %r0, 0
259:
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 259b
	addi %r5, %r23, 0
	addi %r8, %r25, 0
	li %r0, 0
260:
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 260b
	li %r3, 0
	b 258f
257:
	li %r5, 33
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	li %r5, 20
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
	beq %cr0, 261f
	addi %r8, %r29, 0
263:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 263b
	b 262f
261:
	rldicl %r8, %r29, 63, 1
264:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 264b
262:
	li %r10, 20
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	addi %r11, %r29, -2
	addi %r29, %r30, 0
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
	add %r5, %r10, %r29
	add %r8, %r5, %r29
	add %r9, %r8, %r29
	addi %r14, %r5, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
265:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 265b
	rldicr %r14, %r11, 2, 61
	add %r14, %r14, %r5
	addi %r14, %r14, -8
	li %r0, 1
	std %r0, 0(%r14)
	rldicl %r4, %r11, 63, 1
	addi %r4, %r4, 64
266:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
267:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 267b
	stw %r20, 0(%r14)
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
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
269:
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
	bne %cr0, 269b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
270:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 270b
271:
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
	beq %cr0, 272f
274:
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
	bne %cr0, 274b
	b 273f
272:
273:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 275f
277:
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
	bne %cr0, 277b
	b 276f
275:
276:
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
	bne %cr0, 271b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
278:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 278b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
279:
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
	bne %cr0, 279b
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
280:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 280b
281:
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
	beq %cr0, 282f
284:
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
	bne %cr0, 284b
	b 283f
282:
283:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 285f
287:
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
	bne %cr0, 287b
	b 286f
285:
286:
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
	bne %cr0, 281b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
288:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 288b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
289:
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
	bne %cr0, 289b
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
290:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 290b
291:
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
	beq %cr0, 292f
294:
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
	bne %cr0, 294b
	b 293f
292:
293:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 295f
297:
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
	bne %cr0, 297b
	b 296f
295:
296:
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
	bne %cr0, 291b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
298:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 298b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
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
2100:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2100b
2101:
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
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r3, %r3, 8
	addi %r16, %r16, -1
	cmpldi %cr0, %r16, 0
	bne %cr0, 2104b
	b 2103f
2102:
2103:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2105f
2107:
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
	bne %cr0, 2107b
	b 2106f
2105:
2106:
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
	bne %cr0, 2101b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2108:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2108b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2109:
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
	bne %cr0, 2109b
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
2110:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2110b
2111:
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
	beq %cr0, 2112f
2114:
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
	bne %cr0, 2114b
	b 2113f
2112:
2113:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2115f
2117:
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
	bne %cr0, 2117b
	b 2116f
2115:
2116:
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
	bne %cr0, 2111b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2118:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2118b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2119:
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
	bne %cr0, 2119b
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
2120:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2120b
2121:
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
	beq %cr0, 2122f
2124:
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
	bne %cr0, 2124b
	b 2123f
2122:
2123:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2125f
2127:
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
	bne %cr0, 2127b
	b 2126f
2125:
2126:
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
	bne %cr0, 2121b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2128:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2128b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2129:
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
	bne %cr0, 2129b
	addi %r29, %r11, 2
	li %r5, 21
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	addi %r5, %r5, -8
	li %r0, 0
	stw %r0, 0(%r5)
	stw %r0, 4(%r5)
	li %r5, 26
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
	beq %cr0, 2130f
	addi %r8, %r29, 0
2132:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2132b
	b 2131f
2130:
	rldicl %r8, %r29, 63, 1
2133:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2133b
2131:
	li %r10, 20
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	addi %r11, %r29, -2
	addi %r29, %r30, 0
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2134:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2134b
2135:
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
	beq %cr0, 2136f
2138:
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
	bne %cr0, 2138b
	b 2137f
2136:
2137:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2139f
2141:
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
	bne %cr0, 2141b
	b 2140f
2139:
2140:
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
	bne %cr0, 2135b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2142:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2142b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
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
	addi %r29, %r11, 2
	li %r5, 26
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	addi %r5, %r5, -8
	li %r0, 0
	stw %r0, 0(%r5)
	stw %r0, 4(%r5)
	li %r5, 35
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
	beq %cr0, 2144f
	addi %r8, %r29, 0
2146:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2146b
	b 2145f
2144:
	rldicl %r8, %r29, 63, 1
2147:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2147b
2145:
	li %r5, 36
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 32
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 35
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2148f
	addi %r8, %r29, 0
	li %r9, 0
2150:
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
	bne %cr0, 2150b
	b 2149f
2148:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2151:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2151b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2149:
	li %r24, 0
2152:
	li %r5, 25
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 34
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2153f
	addi %r8, %r29, 0
2155:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2155b
	b 2154f
2153:
	rldicl %r8, %r29, 63, 1
2156:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2156b
2154:
	li %r5, 25
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r0, %r24, 2
	stw %r0, 0(%r5)
	li %r5, 24
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
	beq %cr0, 2157f
	addi %r8, %r29, 0
2159:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2159b
	b 2158f
2157:
	rldicl %r8, %r29, 63, 1
2160:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2160b
2158:
	li %r5, 29
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 34
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2161f
	addi %r8, %r29, 0
2163:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2163b
	b 2162f
2161:
	rldicl %r8, %r29, 63, 1
2164:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2164b
2162:
	li %r0, 1
	stw %r0, 8(%r31)
	li %r0, 0
	stw %r0, 12(%r31)
	addi %r27, %r26, 31
	rldicl %r27, %r27, 59, 5
	li %r10, 20
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	addi %r11, %r29, -2
	addi %r29, %r30, 0
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2165:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2165b
2166:
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
	beq %cr0, 2167f
2169:
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
	bne %cr0, 2169b
	b 2168f
2167:
2168:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2170f
2172:
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
	bne %cr0, 2172b
	b 2171f
2170:
2171:
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
	bne %cr0, 2166b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2173:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2173b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2174:
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
	bne %cr0, 2174b
	addi %r29, %r11, 2
	li %r5, 25
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	addi %r5, %r5, -8
	li %r0, 0
	stw %r0, 0(%r5)
	stw %r0, 4(%r5)
2175:
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r27, 2, 61
	add %r5, %r5, %r0
	addi %r5, %r5, -4
	lwz %r0, 0(%r5)
	stw %r0, 0(%r31)
	li %r28, 32
2176:
	lwz %r0, 0(%r31)
	rldicl %r3, %r0, 33, 31
	stw %r3, 16(%r31)
	rldicr %r0, %r0, 1, 62
	stw %r0, 0(%r31)
	li %r10, 20
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	addi %r11, %r29, -2
	addi %r29, %r30, 0
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2177:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2177b
2178:
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
	beq %cr0, 2179f
2181:
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
	bne %cr0, 2181b
	b 2180f
2179:
2180:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2182f
2184:
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
	bne %cr0, 2184b
	b 2183f
2182:
2183:
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
	bne %cr0, 2178b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2185:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2185b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2186:
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
	bne %cr0, 2186b
	addi %r29, %r11, 2
	li %r5, 27
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	addi %r5, %r5, -8
	li %r0, 0
	stw %r0, 0(%r5)
	stw %r0, 4(%r5)
	cmpldi %cr0, %r24, 0
	beq %cr0, 2187f
	addi %r0, %r24, -1
	cmpldi %cr0, %r0, 0
	beq %cr0, 2189f
	li %r10, 20
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	addi %r11, %r29, -2
	addi %r29, %r30, 0
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2191:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2191b
2192:
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
	beq %cr0, 2193f
2195:
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
	bne %cr0, 2195b
	b 2194f
2193:
2194:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2196f
2198:
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
	bne %cr0, 2198b
	b 2197f
2196:
2197:
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
	bne %cr0, 2192b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2199:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2199b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2200:
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
	bne %cr0, 2200b
	addi %r29, %r11, 2
	li %r5, 26
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	addi %r5, %r5, -8
	li %r0, 0
	stw %r0, 0(%r5)
	stw %r0, 4(%r5)
	b 2190f
2189:
	li %r5, 37
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 34
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 27
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2201f
	addi %r8, %r29, 0
	li %r9, 0
2203:
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
	bne %cr0, 2203b
	b 2202f
2201:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2204:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2204b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2202:
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 27
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
	beq %cr0, 2205f
	addi %r8, %r29, 0
	li %r9, 0
2207:
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
	bne %cr0, 2207b
	b 2206f
2205:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2208:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2208b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2206:
	li %r5, 39
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 38
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 32
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2209f
	addi %r8, %r29, 0
	li %r9, 0
2211:
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
	bne %cr0, 2211b
	b 2210f
2209:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2212:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2212b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2210:
	stw %r9, 132(%r31)
	li %r5, 26
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 39
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 38
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2213f
	addi %r8, %r29, 0
2215:
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
	bne %cr0, 2215b
	b 2214f
2213:
	rldicl %r8, %r29, 63, 1
2216:
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
	bne %cr0, 2216b
2214:
	li %r5, 37
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 34
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 27
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2217f
	addi %r8, %r29, 0
	li %r9, 0
2219:
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
	bne %cr0, 2219b
	b 2218f
2217:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2220:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2220b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2218:
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 26
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
	beq %cr0, 2221f
	addi %r8, %r29, 0
	li %r9, 0
2223:
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
	bne %cr0, 2223b
	b 2222f
2221:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2224:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2224b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2222:
	li %r5, 39
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 38
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 32
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2225f
	addi %r8, %r29, 0
	li %r9, 0
2227:
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
	bne %cr0, 2227b
	b 2226f
2225:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2228:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2228b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2226:
	stw %r9, 132(%r31)
	li %r5, 26
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 39
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 38
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2229f
	addi %r8, %r29, 0
2231:
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
	bne %cr0, 2231b
	b 2230f
2229:
	rldicl %r8, %r29, 63, 1
2232:
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
	bne %cr0, 2232b
2230:
2190:
	b 2188f
2187:
	li %r5, 37
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 34
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 27
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2233f
	addi %r8, %r29, 0
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
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2234:
	li %r5, 38
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 27
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
	beq %cr0, 2237f
	addi %r8, %r29, 0
	li %r9, 0
2239:
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
	bne %cr0, 2239b
	b 2238f
2237:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2240:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2240b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2238:
	li %r5, 39
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 38
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 32
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2241f
	addi %r8, %r29, 0
	li %r9, 0
2243:
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
	bne %cr0, 2243b
	b 2242f
2241:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2244:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2244b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2242:
	stw %r9, 132(%r31)
	li %r5, 26
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 39
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 38
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 132(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2245f
	addi %r8, %r29, 0
2247:
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
	bne %cr0, 2247b
	b 2246f
2245:
	rldicl %r8, %r29, 63, 1
2248:
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
	bne %cr0, 2248b
2246:
2188:
	li %r5, 28
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 27
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 26
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 16(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2249f
	addi %r8, %r29, 0
2251:
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
	bne %cr0, 2251b
	b 2250f
2249:
	rldicl %r8, %r29, 63, 1
2252:
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
	bne %cr0, 2252b
2250:
	li %r6, 28
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 35
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2253f
	addi %r8, %r29, 0
2255:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2255b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 24(%r31)
	b 2254f
2253:
	rldicl %r8, %r29, 63, 1
2256:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2256b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 24(%r31)
2254:
	li %r6, 28
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 36
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2257f
	addi %r8, %r29, 0
2259:
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 4
	addi %r7, %r7, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2259b
	li %r0, 0
	subf %r0, %r9, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 28(%r31)
	b 2258f
2257:
	rldicl %r8, %r29, 63, 1
2260:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	xor %r0, %r0, %r3
	or %r9, %r9, %r0
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2260b
	li %r0, 0
	subf %r0, %r9, %r0
	or %r0, %r0, %r9
	rldicl %r0, %r0, 1, 63
	li %r3, 1
	xor %r0, %r0, %r3
	stw %r0, 28(%r31)
2258:
	lwz %r3, 16(%r31)
	lwz %r4, 8(%r31)
	lwz %r5, 24(%r31)
	lwz %r6, 28(%r31)
	lwz %r7, 12(%r31)
	li %r0, 1
	xor %r3, %r3, %r0
	xor %r8, %r4, %r0
	and %r8, %r8, %r3
	and %r8, %r8, %r5
	stw %r8, 20(%r31)
	or %r7, %r7, %r8
	and %r7, %r7, %r3
	stw %r7, 12(%r31)
	and %r4, %r4, %r3
	or %r4, %r4, %r5
	or %r4, %r4, %r6
	stw %r4, 8(%r31)
	li %r5, 29
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 29
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 24
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 20(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2261f
	addi %r8, %r29, 0
2263:
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
	bne %cr0, 2263b
	b 2262f
2261:
	rldicl %r8, %r29, 63, 1
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
2262:
	li %r5, 24
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 28
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2265f
	addi %r8, %r29, 0
2267:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2267b
	b 2266f
2265:
	rldicl %r8, %r29, 63, 1
2268:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2268b
2266:
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 2176b
	addi %r27, %r27, -1
	cmpldi %cr0, %r27, 0
	bne %cr0, 2175b
	li %r5, 24
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 34
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 29
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 12(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2269f
	addi %r8, %r29, 0
2271:
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
	bne %cr0, 2271b
	b 2270f
2269:
	rldicl %r8, %r29, 63, 1
2272:
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
	bne %cr0, 2272b
2270:
	addi %r24, %r24, 1
	addi %r0, %r24, -100
	rldicl %r0, %r0, 1, 63
	lwz %r3, 12(%r31)
	li %r4, 1
	xor %r3, %r3, %r4
	and %r0, %r0, %r3
	cmpldi %cr0, %r0, 0
	bne %cr0, 2152b
	lwz %r0, 12(%r31)
	stw %r0, 152(%r31)
	li %r5, 26
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
	li %r10, 20
	mulld %r10, %r10, %r30
	add %r10, %r10, %r31
	addi %r10, %r10, 160
	addi %r11, %r29, -2
	addi %r29, %r30, 0
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
	rldicl %r4, %r11, 63, 1
	addi %r14, %r8, 0
	addi %r17, %r4, 1
	li %r22, 0
2277:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2277b
2278:
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
	beq %cr0, 2279f
2281:
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
	bne %cr0, 2281b
	b 2280f
2279:
2280:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2282f
2284:
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
	bne %cr0, 2284b
	b 2283f
2282:
2283:
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
	bne %cr0, 2278b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2285:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2285b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2286:
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
	bne %cr0, 2286b
	addi %r29, %r11, 2
	li %r5, 24
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	addi %r5, %r5, -8
	li %r0, 0
	stw %r0, 0(%r5)
	stw %r0, 4(%r5)
	li %r5, 0
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 24
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 33
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2287f
	addi %r8, %r29, 0
	li %r9, 0
2289:
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
	bne %cr0, 2289b
	b 2288f
2287:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2290:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2290b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2288:
	li %r5, 1
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
	beq %cr0, 2291f
	addi %r8, %r29, 0
2293:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2293b
	b 2292f
2291:
	rldicl %r8, %r29, 63, 1
2294:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2294b
2292:
	li %r5, 8
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
	beq %cr0, 2295f
	addi %r8, %r29, 0
2297:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2297b
	b 2296f
2295:
	rldicl %r8, %r29, 63, 1
2298:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2298b
2296:
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 34
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2299f
	addi %r8, %r29, 0
2301:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2301b
	b 2300f
2299:
	rldicl %r8, %r29, 63, 1
2302:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2302b
2300:
	li %r5, 2
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	stw %r0, 0(%r5)
	li %r5, 3
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 34
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2303f
	addi %r8, %r29, 0
2305:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2305b
	b 2304f
2303:
	rldicl %r8, %r29, 63, 1
2306:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2306b
2304:
	li %r5, 10
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 34
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2307f
	addi %r8, %r29, 0
2309:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2309b
	b 2308f
2307:
	rldicl %r8, %r29, 63, 1
2310:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2310b
2308:
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
	beq %cr0, 2311f
	addi %r8, %r29, 0
	li %r9, 0
2313:
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
	bne %cr0, 2313b
	b 2312f
2311:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2314:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2314b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2312:
	rldicr %r4, %r29, 5, 58
2315:
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
	beq %cr0, 2316f
	addi %r8, %r29, 0
	li %r9, 0
2318:
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
	bne %cr0, 2318b
	b 2317f
2316:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2319:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2319b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2317:
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
	beq %cr0, 2320f
	addi %r8, %r29, 0
	li %r9, 0
2322:
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
	bne %cr0, 2322b
	b 2321f
2320:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2323:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2323b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2321:
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
	beq %cr0, 2324f
	addi %r8, %r29, 0
2326:
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
	bne %cr0, 2326b
	b 2325f
2324:
	rldicl %r8, %r29, 63, 1
2327:
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
	bne %cr0, 2327b
2325:
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
	beq %cr0, 2328f
	addi %r8, %r29, 0
2330:
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
	bne %cr0, 2330b
	b 2329f
2328:
	rldicl %r8, %r29, 63, 1
2331:
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
	bne %cr0, 2331b
2329:
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
	beq %cr0, 2332f
	addi %r8, %r29, 0
2334:
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
	bne %cr0, 2334b
	b 2333f
2332:
	rldicl %r8, %r29, 63, 1
2335:
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
	bne %cr0, 2335b
2333:
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
	beq %cr0, 2336f
	addi %r8, %r29, 0
2338:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2338b
	b 2337f
2336:
	rldicl %r8, %r29, 63, 1
2339:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2339b
2337:
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
	beq %cr0, 2340f
	addi %r8, %r29, 0
	li %r9, 0
2342:
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
	bne %cr0, 2342b
	b 2341f
2340:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2343:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2343b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2341:
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
	beq %cr0, 2344f
	addi %r8, %r29, 0
2346:
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
	bne %cr0, 2346b
	b 2345f
2344:
	rldicl %r8, %r29, 63, 1
2347:
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
	bne %cr0, 2347b
2345:
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
	beq %cr0, 2348f
	addi %r8, %r29, 0
	li %r9, 0
2350:
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
	bne %cr0, 2350b
	b 2349f
2348:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2351:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2351b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2349:
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
	beq %cr0, 2352f
	addi %r8, %r29, 0
	li %r9, 0
2354:
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
	bne %cr0, 2354b
	b 2353f
2352:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2355:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2355b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2353:
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
	beq %cr0, 2356f
	addi %r8, %r29, 0
2358:
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
	bne %cr0, 2358b
	b 2357f
2356:
	rldicl %r8, %r29, 63, 1
2359:
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
	bne %cr0, 2359b
2357:
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
	beq %cr0, 2360f
	addi %r8, %r29, 0
	li %r9, 0
2362:
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
	bne %cr0, 2362b
	b 2361f
2360:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2363:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2363b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2361:
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
	beq %cr0, 2364f
	addi %r8, %r29, 0
2366:
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
	bne %cr0, 2366b
	b 2365f
2364:
	rldicl %r8, %r29, 63, 1
2367:
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
	bne %cr0, 2367b
2365:
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
	beq %cr0, 2368f
	addi %r8, %r29, 0
2370:
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
	bne %cr0, 2370b
	b 2369f
2368:
	rldicl %r8, %r29, 63, 1
2371:
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
	bne %cr0, 2371b
2369:
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
	beq %cr0, 2372f
	addi %r8, %r29, 0
2374:
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
	bne %cr0, 2374b
	b 2373f
2372:
	rldicl %r8, %r29, 63, 1
2375:
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
	bne %cr0, 2375b
2373:
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
	beq %cr0, 2376f
	addi %r8, %r29, 0
2378:
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
	bne %cr0, 2378b
	b 2377f
2376:
	rldicl %r8, %r29, 63, 1
2379:
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
	bne %cr0, 2379b
2377:
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
	beq %cr0, 2380f
	addi %r8, %r29, 0
	li %r9, 0
2382:
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
	bne %cr0, 2382b
	b 2381f
2380:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2383:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2383b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2381:
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
	beq %cr0, 2384f
	addi %r8, %r29, 0
2386:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2386b
	b 2385f
2384:
	rldicl %r8, %r29, 63, 1
2387:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2387b
2385:
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
	beq %cr0, 2388f
	addi %r8, %r29, 0
	li %r9, 0
2390:
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
	bne %cr0, 2390b
	b 2389f
2388:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2391:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2391b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2389:
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
	beq %cr0, 2392f
	addi %r8, %r29, 0
	li %r9, 0
2394:
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
	bne %cr0, 2394b
	b 2393f
2392:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2395:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2395b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2393:
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
	beq %cr0, 2396f
	addi %r8, %r29, 0
2398:
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
	bne %cr0, 2398b
	b 2397f
2396:
	rldicl %r8, %r29, 63, 1
2399:
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
	bne %cr0, 2399b
2397:
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
	beq %cr0, 2400f
	addi %r8, %r29, 0
2402:
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
	bne %cr0, 2402b
	b 2401f
2400:
	rldicl %r8, %r29, 63, 1
2403:
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
	bne %cr0, 2403b
2401:
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
	beq %cr0, 2404f
	addi %r8, %r29, 0
2406:
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
	bne %cr0, 2406b
	b 2405f
2404:
	rldicl %r8, %r29, 63, 1
2407:
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
	bne %cr0, 2407b
2405:
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
	beq %cr0, 2408f
	addi %r8, %r29, 0
2410:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2410b
	b 2409f
2408:
	rldicl %r8, %r29, 63, 1
2411:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2411b
2409:
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
	beq %cr0, 2412f
	addi %r8, %r29, 0
	li %r9, 0
2414:
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
	bne %cr0, 2414b
	b 2413f
2412:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2415:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2415b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2413:
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
	beq %cr0, 2420f
	addi %r8, %r29, 0
	li %r9, 0
2422:
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
	bne %cr0, 2422b
	b 2421f
2420:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2423:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2423b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2421:
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
	beq %cr0, 2436f
	addi %r8, %r29, 0
2438:
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
	bne %cr0, 2438b
	b 2437f
2436:
	rldicl %r8, %r29, 63, 1
2439:
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
	bne %cr0, 2439b
2437:
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
	beq %cr0, 2444f
	addi %r8, %r29, 0
2446:
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
	bne %cr0, 2446b
	b 2445f
2444:
	rldicl %r8, %r29, 63, 1
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
2445:
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
	beq %cr0, 2452f
	addi %r8, %r29, 0
	li %r9, 0
2454:
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
	bne %cr0, 2454b
	b 2453f
2452:
	rldicl %r8, %r29, 63, 1
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
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2453:
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
	beq %cr0, 2456f
	addi %r8, %r29, 0
2458:
	lwz %r0, 0(%r5)
	lwz %r3, 4(%r5)
	rldicr %r3, %r3, 31, 32
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2458b
	b 2457f
2456:
	rldicl %r8, %r29, 63, 1
2459:
	ld %r0, 0(%r5)
	lwz %r3, 8(%r5)
	rldicr %r3, %r3, 63, 0
	rldicl %r0, %r0, 63, 1
	or %r0, %r0, %r3
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2459b
2457:
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2315b
	li %r5, 40
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
	beq %cr0, 2460f
	addi %r8, %r29, 0
2462:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2462b
	b 2461f
2460:
	rldicl %r8, %r29, 63, 1
2463:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2463b
2461:
	li %r5, 42
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2464f
	addi %r8, %r29, 0
2466:
	lwz %r0, 0(%r6)
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r6, %r6, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2466b
	b 2465f
2464:
	rldicl %r8, %r29, 63, 1
2467:
	ld %r0, 0(%r6)
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2467b
2465:
	li %r5, 42
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	rldicr %r0, %r29, 2, 61
	add %r5, %r5, %r0
	li %r0, 0
	stw %r0, 0(%r5)
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	addi %r8, %r29, 1
	li %r0, 0
2468:
	stw %r0, 0(%r5)
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2468b
	rldicr %r4, %r29, 5, 58
2469:
	li %r5, 40
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r9, 0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2470f
	addi %r8, %r29, 0
2472:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2472b
	b 2471f
2470:
	rldicl %r8, %r29, 63, 1
2473:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2473b
2471:
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2474f
	addi %r8, %r29, 1
2476:
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2476b
	b 2475f
2474:
	rldicl %r8, %r29, 63, 1
2477:
	ld %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	std %r3, 0(%r5)
	rldicl %r9, %r0, 1, 63
	addi %r5, %r5, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2477b
	lwz %r0, 0(%r5)
	rldicr %r3, %r0, 1, 62
	or %r3, %r3, %r9
	stw %r3, 0(%r5)
	rldicl %r9, %r0, 33, 31
	addi %r5, %r5, 4
2475:
	li %r5, 43
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 41
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 42
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2478f
	addi %r8, %r29, 1
	li %r9, 0
2480:
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
	bne %cr0, 2480b
	b 2479f
2478:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2481:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2481b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	subfe %r0, %r3, %r0
	stw %r0, 0(%r5)
	rldicl %r9, %r0, 1, 63
2479:
	li %r10, 1
	xor %r10, %r10, %r9
	li %r0, 0
	subf %r9, %r10, %r0
	li %r5, 41
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 41
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 43
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2482f
	addi %r8, %r29, 1
2484:
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
	bne %cr0, 2484b
	b 2483f
2482:
	rldicl %r8, %r29, 63, 1
2485:
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
	bne %cr0, 2485b
	lwz %r0, 0(%r6)
	lwz %r3, 0(%r7)
	xor %r3, %r3, %r0
	and %r3, %r3, %r9
	xor %r3, %r3, %r0
	stw %r3, 0(%r5)
2483:
	li %r5, 40
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	lwz %r0, 0(%r5)
	or %r0, %r0, %r10
	stw %r0, 0(%r5)
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2469b
	li %r5, 37
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 40
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2486f
	addi %r8, %r29, 0
	li %r9, 0
2488:
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
	bne %cr0, 2488b
	b 2487f
2486:
	rldicl %r8, %r29, 63, 1
	subfc %r0, %r8, %r8
2489:
	ld %r0, 0(%r6)
	ld %r3, 0(%r7)
	subfe %r0, %r3, %r0
	std %r0, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, 8
	addi %r7, %r7, 8
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2489b
	li %r9, 0
	adde %r9, %r9, %r9
	li %r0, 1
	xor %r9, %r9, %r0
2487:
	stw %r9, 32(%r31)
	li %r5, 5
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 1
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 40
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 32(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2490f
	addi %r8, %r29, 0
2492:
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
	bne %cr0, 2492b
	b 2491f
2490:
	rldicl %r8, %r29, 63, 1
2493:
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
	bne %cr0, 2493b
2491:
	li %r5, 6
	mulld %r5, %r5, %r30
	add %r5, %r5, %r31
	addi %r5, %r5, 160
	li %r6, 40
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	li %r7, 1
	mulld %r7, %r7, %r30
	add %r7, %r7, %r31
	addi %r7, %r7, 160
	lwz %r9, 32(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r0, 1
	and %r0, %r29, %r0
	cmpldi %cr0, %r0, 0
	beq %cr0, 2494f
	addi %r8, %r29, 0
2496:
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
	bne %cr0, 2496b
	b 2495f
2494:
	rldicl %r8, %r29, 63, 1
2497:
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
	bne %cr0, 2497b
2495:
	addi %r5, %r21, 0
	addi %r8, %r25, 0
	lwz %r9, 152(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 5
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2498:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2498b
	addi %r5, %r23, 0
	addi %r8, %r25, 0
	lwz %r9, 152(%r31)
	li %r0, 0
	subf %r9, %r9, %r0
	li %r6, 6
	mulld %r6, %r6, %r30
	add %r6, %r6, %r31
	addi %r6, %r6, 160
	add %r6, %r6, %r8
	addi %r6, %r6, -1
2499:
	lbz %r0, 0(%r6)
	and %r0, %r0, %r9
	stb %r0, 0(%r5)
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2499b
	lwz %r3, 152(%r31)
258:
25:
	li %r11, 44
	mulld %r11, %r11, %r30
	add %r11, %r11, %r31
	addi %r11, %r11, 160
	ld %r14, 0(%r11)
	ld %r15, 8(%r11)
	ld %r16, 16(%r11)
	ld %r17, 24(%r11)
	ld %r18, 32(%r11)
	ld %r19, 40(%r11)
	ld %r20, 48(%r11)
	ld %r21, 56(%r11)
	ld %r22, 64(%r11)
	ld %r23, 72(%r11)
	ld %r24, 80(%r11)
	ld %r25, 88(%r11)
	ld %r26, 96(%r11)
	ld %r27, 104(%r11)
	ld %r28, 112(%r11)
	ld %r29, 120(%r11)
	ld %r30, 128(%r11)
	ld %r31, 136(%r11)
	blr
