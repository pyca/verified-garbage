// The functions of `src/internal/vg_ffdh_parameter_candidate.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ffdh_parameter_candidate:
	addi %r11, %r1, 96
	ld %r12, 0(%r11)
	rldicr %r11, %r12, 3, 60
	add %r11, %r10, %r11
	addi %r11, %r11, -160
	mflr %r0
	std %r0, 144(%r11)
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
	std %r25, 88(%r11)
	std %r26, 96(%r11)
	std %r27, 104(%r11)
	std %r28, 112(%r11)
	std %r29, 120(%r11)
	std %r30, 128(%r11)
	std %r31, 136(%r11)
	addi %r31, %r10, 0
	std %r12, 0(%r31)
	std %r3, 16(%r31)
	std %r4, 24(%r31)
	std %r4, 152(%r31)
	std %r5, 32(%r31)
	std %r6, 40(%r31)
	rlwinm %r7, %r7, 0, 0, 31
	std %r7, 128(%r31)
	std %r8, 136(%r31)
	std %r9, 144(%r31)
	ld %r4, 16(%r31)
	ld %r5, 24(%r31)
	li %r0, 0
20:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	ld %r3, 144(%r31)
	ld %r4, 24(%r31)
	subf %r5, %r4, %r3
	rldicl %r5, %r5, 1, 63
	li %r0, 1
	xor %r5, %r5, %r0
	rldicl %r0, %r3, 1, 63
	or %r5, %r5, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 21f
	ld %r3, 40(%r31)
	std %r3, 248(%r31)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	std %r4, 216(%r31)
	addi %r4, %r3, 63
	rldicl %r4, %r4, 58, 6
	std %r4, 48(%r31)
	rldicr %r11, %r4, 1, 62
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	std %r29, 224(%r31)
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	std %r5, 64(%r31)
	add %r5, %r5, %r29
	std %r5, 72(%r31)
	add %r5, %r5, %r29
	std %r5, 80(%r31)
	add %r5, %r5, %r29
	std %r5, 88(%r31)
	add %r5, %r5, %r29
	std %r5, 96(%r31)
	add %r5, %r5, %r29
	std %r5, 104(%r31)
	add %r5, %r5, %r29
	std %r5, 112(%r31)
	add %r5, %r5, %r29
	std %r5, 120(%r31)
	add %r5, %r5, %r29
	addi %r5, %r3, -2049
	rldicl %r5, %r5, 1, 63
	rldicr %r5, %r5, 6, 57
	li %r6, 128
	subf %r5, %r5, %r6
	std %r5, 168(%r31)
	ld %r3, 248(%r31)
	ld %r4, 48(%r31)
	rldicr %r4, %r4, 6, 57
	subf %r3, %r4, %r3
	addi %r3, %r3, 64
	li %r5, 0
23:
	add %r5, %r5, %r5
	addi %r5, %r5, 1
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 23b
	std %r5, 192(%r31)
	ld %r12, 136(%r31)
	ld %r6, 24(%r31)
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
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	addi %r5, %r5, -8
	ld %r4, 192(%r31)
	ld %r6, 0(%r5)
	and %r6, %r6, %r4
	rldicl %r4, %r4, 63, 1
	addi %r4, %r4, 1
	or %r6, %r6, %r4
	std %r6, 0(%r5)
	ld %r6, 0(%r10)
	li %r4, 1
	or %r6, %r6, %r4
	std %r6, 0(%r10)
	ld %r3, 128(%r31)
	addi %r3, %r3, -2
	cmpldi %cr0, %r3, 0
	beq %cr0, 26f
	li %r4, 10
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
28:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
29:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 29b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 28b
	li %r4, 4
	or %r3, %r3, %r4
	li %r4, 7
	xor %r3, %r3, %r4
	std %r3, 200(%r31)
	b 27f
26:
	li %r4, 24
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
210:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
211:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 211b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 210b
	li %r4, 11
	xor %r3, %r3, %r4
	std %r3, 200(%r31)
27:
	ld %r5, 200(%r31)
	cmpldi %cr0, %r5, 0
	beq %cr0, 212f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 213f
212:
	ld %r22, 200(%r31)
	li %r4, 3
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
214:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
215:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 215b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 214b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 5
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
216:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
217:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 217b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 216b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 7
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
218:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
219:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 219b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 218b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 11
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
220:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
221:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 221b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 220b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 13
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
222:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
223:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 223b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 222b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 17
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
224:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
225:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 225b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 224b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 19
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
226:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
227:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 227b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 226b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 23
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
228:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
229:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 229b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 228b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 29
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
230:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
231:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 231b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 230b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 31
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
232:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
233:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 233b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 232b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 37
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
234:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
235:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 235b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 234b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 41
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
236:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
237:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 237b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 236b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 43
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
238:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
239:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 239b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 238b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 47
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
240:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
241:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 241b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 240b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 53
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
242:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
243:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 243b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 242b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 59
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
244:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
245:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 245b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 244b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 61
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
246:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
247:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 247b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 246b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 67
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
248:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
249:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 249b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 248b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 71
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
250:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
251:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 251b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 250b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 73
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
252:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
253:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 253b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 252b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 79
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
254:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
255:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 255b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 254b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 83
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
256:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
257:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 257b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 256b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 89
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
258:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
259:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 259b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 258b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 97
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
260:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
261:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 261b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 260b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 101
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
262:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
263:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 263b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 262b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 103
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
264:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
265:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 265b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 264b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 107
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
266:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
267:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 267b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 266b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 109
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
268:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
269:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 269b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 268b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 113
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
270:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
271:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 271b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 270b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 127
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
272:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
273:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 273b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 272b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 131
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
274:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
275:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 275b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 274b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 137
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
276:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
277:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 277b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 276b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 139
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
278:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
279:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 279b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 278b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 149
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
280:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
281:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 281b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 280b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 151
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
282:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
283:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 283b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 282b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 157
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
284:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
285:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 285b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 284b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 163
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
286:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
287:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 287b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 286b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 167
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
288:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
289:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 289b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 288b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 173
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
290:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
291:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 291b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 290b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 179
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
292:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
293:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 293b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 292b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 181
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
294:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
295:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 295b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 294b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 191
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
296:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
297:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 297b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 296b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 193
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
298:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
299:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 299b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 298b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 197
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2100:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2101:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2101b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2100b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 199
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2102:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2103:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2103b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2102b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 211
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2104:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2105:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2105b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2104b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 223
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2106:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2107:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2107b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2106b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 227
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2108:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2109:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2109b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2108b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 229
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2110:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2111:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2111b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2110b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 233
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2112:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2113:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2113b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2112b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 239
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2114:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2115:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2115b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2114b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 241
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2116:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2117:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2117b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2116b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 251
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2118:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2119:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2119b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2118b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	std %r22, 200(%r31)
	addi %r5, %r10, 0
	rldicl %r6, %r11, 63, 1
	addi %r6, %r6, -1
2120:
	ld %r3, 0(%r5)
	ld %r4, 8(%r5)
	rldicl %r3, %r3, 63, 1
	rldicr %r4, %r4, 63, 0
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2120b
	ld %r3, 0(%r5)
	rldicl %r3, %r3, 63, 1
	std %r3, 0(%r5)
	ld %r5, 200(%r31)
	ld %r3, 0(%r10)
	li %r4, 1
	and %r3, %r3, %r4
	xor %r3, %r3, %r4
	or %r5, %r5, %r3
	std %r5, 200(%r31)
	ld %r22, 200(%r31)
	li %r4, 3
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2121:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2122:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2122b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2121b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 5
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2123:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2124:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2124b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2123b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 7
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2125:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2126:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2126b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2125b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 11
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2127:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2128:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2128b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2127b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 13
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2129:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2130:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2130b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2129b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 17
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2131:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2132:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2132b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2131b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 19
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2133:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2134:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2134b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2133b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 23
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2135:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2136:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2136b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2135b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 29
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2137:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2138:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2138b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2137b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 31
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2139:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2140:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2140b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2139b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 37
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2141:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2142:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2142b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2141b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 41
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2143:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2144:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2144b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2143b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 43
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2145:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2146:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2146b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2145b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 47
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2147:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2148:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2148b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2147b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 53
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2149:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2150:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2150b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2149b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 59
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2151:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2152:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2152b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2151b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 61
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2153:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2154:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2154b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2153b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 67
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2155:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2156:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2156b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2155b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 71
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2157:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2158:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2158b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2157b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 73
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2159:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2160:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2160b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2159b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 79
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2161:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2162:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2162b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2161b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 83
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2163:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2164:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2164b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2163b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 89
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2165:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2166:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2166b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2165b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 97
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2167:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2168:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2168b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2167b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 101
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2169:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2170:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2170b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2169b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 103
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2171:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2172:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2172b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2171b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 107
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2173:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2174:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2174b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2173b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 109
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2175:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2176:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2176b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2175b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 113
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2177:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2178:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2178b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2177b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 127
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2179:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2180:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2180b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2179b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 131
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2181:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2182:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2182b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2181b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 137
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2183:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2184:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2184b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2183b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 139
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2185:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2186:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2186b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2185b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 149
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2187:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2188:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2188b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2187b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 151
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2189:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2190:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2190b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2189b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 157
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2191:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2192:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2192b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2191b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 163
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2193:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2194:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2194b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2193b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 167
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2195:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2196:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2196b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2195b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 173
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2197:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2198:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2198b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2197b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 179
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2199:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2200:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2200b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2199b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 181
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2201:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2202:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2202b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2201b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 191
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2203:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2204:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2204b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2203b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 193
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2205:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2206:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2206b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2205b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 197
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2207:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2208:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2208b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2207b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 199
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2209:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2210:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2210b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2209b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 211
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2211:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2212:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2212b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2211b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 223
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2213:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2214:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2214b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2213b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 227
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2215:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2216:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2216b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2215b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 229
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2217:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2218:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2218b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2217b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 233
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2219:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2220:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2220b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2219b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 239
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2221:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2222:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2222b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2221b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 241
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2223:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2224:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2224b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2223b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	li %r4, 251
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	rldicl %r6, %r11, 63, 1
	li %r3, 0
2225:
	addi %r5, %r5, -8
	ld %r7, 0(%r5)
	li %r8, 64
2226:
	rldicl %r9, %r7, 1, 63
	rldicr %r7, %r7, 1, 62
	add %r3, %r3, %r3
	add %r3, %r3, %r9
	subf %r9, %r4, %r3
	rldicl %r14, %r9, 1, 63
	addi %r14, %r14, -1
	xor %r9, %r9, %r3
	and %r9, %r9, %r14
	xor %r3, %r3, %r9
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 2226b
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2225b
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	or %r22, %r22, %r3
	std %r22, 200(%r31)
	ld %r5, 200(%r31)
	cmpldi %cr0, %r5, 0
	beq %cr0, 2227f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 2228f
2227:
	ld %r3, 40(%r31)
	addi %r3, %r3, -1
	std %r3, 248(%r31)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	std %r4, 216(%r31)
	addi %r4, %r3, 63
	rldicl %r4, %r4, 58, 6
	std %r4, 48(%r31)
	rldicr %r11, %r4, 1, 62
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	std %r29, 224(%r31)
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	std %r5, 64(%r31)
	add %r5, %r5, %r29
	std %r5, 72(%r31)
	add %r5, %r5, %r29
	std %r5, 80(%r31)
	add %r5, %r5, %r29
	std %r5, 88(%r31)
	add %r5, %r5, %r29
	std %r5, 96(%r31)
	add %r5, %r5, %r29
	std %r5, 104(%r31)
	add %r5, %r5, %r29
	std %r5, 112(%r31)
	add %r5, %r5, %r29
	std %r5, 120(%r31)
	add %r5, %r5, %r29
	addi %r5, %r3, -2049
	rldicl %r5, %r5, 1, 63
	rldicr %r5, %r5, 6, 57
	li %r6, 128
	subf %r5, %r5, %r6
	std %r5, 168(%r31)
	ld %r3, 248(%r31)
	ld %r4, 48(%r31)
	rldicr %r4, %r4, 6, 57
	subf %r3, %r4, %r3
	addi %r3, %r3, 64
	li %r5, 0
2229:
	add %r5, %r5, %r5
	addi %r5, %r5, 1
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 2229b
	std %r5, 192(%r31)
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
2230:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2230b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 6, 57
2231:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
2232:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2232b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2233:
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
	bne %cr0, 2233b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
2234:
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
	bne %cr0, 2234b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2231b
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
2235:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2235b
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
2236:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2236b
2237:
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
	beq %cr0, 2238f
2240:
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
	bne %cr0, 2240b
	b 2239f
2238:
2239:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2241f
2243:
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
	bne %cr0, 2243b
	b 2242f
2241:
2242:
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
	bne %cr0, 2237b
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
2246:
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
	bne %cr0, 2246b
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
2247:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2247b
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r6, 0
	li %r4, 1
2248:
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
	bne %cr0, 2248b
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
2249:
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
	bne %cr0, 2249b
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
2250:
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
	bne %cr0, 2250b
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
2251:
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
	bne %cr0, 2251b
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
2252:
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
	bne %cr0, 2252b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	li %r3, 0
	std %r3, 176(%r31)
	li %r3, 4
	std %r3, 160(%r31)
2253:
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
	beq %cr0, 2254f
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
2256:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2256b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2257:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2257b
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	addi %r5, %r5, -8
	ld %r4, 192(%r31)
	ld %r6, 0(%r5)
	and %r6, %r6, %r4
	std %r6, 0(%r5)
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r24, 0(%r5)
	rldicl %r24, %r24, 63, 1
	addi %r5, %r5, 8
	rldicl %r6, %r11, 63, 1
	addi %r6, %r6, -1
2258:
	ld %r3, 0(%r5)
	or %r24, %r24, %r3
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2258b
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
2259:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2259b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r3, 0(%r5)
	li %r4, 1
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	li %r0, 0
	std %r0, 0(%r5)
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
2260:
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
	bne %cr0, 2260b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	cmpldi %cr0, %r24, 0
	beq %cr0, 2261f
	cmpldi %cr0, %r20, 0
	beq %cr0, 2263f
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
2265:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2265b
2266:
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
	beq %cr0, 2267f
2269:
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
	bne %cr0, 2269b
	b 2268f
2267:
2268:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2270f
2272:
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
	bne %cr0, 2272b
	b 2271f
2270:
2271:
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
	bne %cr0, 2266b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2273:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2273b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2274:
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
	bne %cr0, 2274b
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
	beq %cr0, 2275f
	ld %r3, 176(%r31)
	ld %r4, 168(%r31)
	addi %r3, %r3, 1
	std %r3, 176(%r31)
	subf %r4, %r3, %r4
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 3
	mulld %r4, %r4, %r5
	li %r5, 4
	subf %r4, %r4, %r5
	std %r4, 160(%r31)
	b 2276f
2275:
	li %r3, 2
	std %r3, 160(%r31)
2276:
	b 2264f
2263:
2264:
	b 2262f
2261:
2262:
	b 2255f
2254:
	li %r3, 0
	std %r3, 160(%r31)
2255:
	ld %r3, 160(%r31)
	addi %r3, %r3, -4
	cmpldi %cr0, %r3, 0
	beq %cr0, 2253b
	ld %r3, 160(%r31)
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 2277f
	ld %r3, 160(%r31)
	cmpldi %cr0, %r3, 0
	beq %cr0, 2279f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 2280f
2279:
	ld %r4, 32(%r31)
	li %r5, 0
	std %r5, 0(%r4)
	li %r3, 0
2280:
	b 2278f
2277:
	ld %r3, 40(%r31)
	std %r3, 248(%r31)
	addi %r4, %r3, 7
	rldicl %r4, %r4, 61, 3
	std %r4, 216(%r31)
	addi %r4, %r3, 63
	rldicl %r4, %r4, 58, 6
	std %r4, 48(%r31)
	rldicr %r11, %r4, 1, 62
	rldicr %r29, %r4, 3, 60
	addi %r29, %r29, 16
	std %r29, 224(%r31)
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	std %r5, 64(%r31)
	add %r5, %r5, %r29
	std %r5, 72(%r31)
	add %r5, %r5, %r29
	std %r5, 80(%r31)
	add %r5, %r5, %r29
	std %r5, 88(%r31)
	add %r5, %r5, %r29
	std %r5, 96(%r31)
	add %r5, %r5, %r29
	std %r5, 104(%r31)
	add %r5, %r5, %r29
	std %r5, 112(%r31)
	add %r5, %r5, %r29
	std %r5, 120(%r31)
	add %r5, %r5, %r29
	addi %r5, %r3, -2049
	rldicl %r5, %r5, 1, 63
	rldicr %r5, %r5, 6, 57
	li %r6, 128
	subf %r5, %r5, %r6
	std %r5, 168(%r31)
	ld %r3, 248(%r31)
	ld %r4, 48(%r31)
	rldicr %r4, %r4, 6, 57
	subf %r3, %r4, %r3
	addi %r3, %r3, 64
	li %r5, 0
2281:
	add %r5, %r5, %r5
	addi %r5, %r5, 1
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 2281b
	std %r5, 192(%r31)
	ld %r12, 136(%r31)
	ld %r6, 24(%r31)
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r0, 0
2282:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2282b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2283:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2283b
	rldicr %r5, %r11, 2, 61
	add %r5, %r10, %r5
	addi %r5, %r5, -8
	ld %r4, 192(%r31)
	ld %r6, 0(%r5)
	and %r6, %r6, %r4
	rldicl %r4, %r4, 63, 1
	addi %r4, %r4, 1
	or %r6, %r6, %r4
	std %r6, 0(%r5)
	ld %r6, 0(%r10)
	li %r4, 1
	or %r6, %r6, %r4
	std %r6, 0(%r10)
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
2284:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2284b
	li %r0, 1
	stw %r0, 0(%r5)
	rldicr %r4, %r11, 6, 57
2285:
	addi %r14, %r8, 0
	addi %r15, %r5, 0
	addi %r17, %r11, 0
	li %r20, 0
2286:
	lwz %r0, 0(%r15)
	add %r0, %r0, %r0
	add %r0, %r0, %r20
	stw %r0, 0(%r14)
	rldicl %r20, %r0, 32, 32
	addi %r14, %r14, 4
	addi %r15, %r15, 4
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2286b
	stw %r20, 0(%r14)
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	addi %r17, %r11, 0
	li %r20, 0
2287:
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
	bne %cr0, 2287b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	addi %r17, %r11, 0
2288:
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
	bne %cr0, 2288b
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 2285b
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
2289:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2289b
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
2290:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2290b
2291:
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
	beq %cr0, 2292f
2294:
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
	bne %cr0, 2294b
	b 2293f
2292:
2293:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2295f
2297:
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
	bne %cr0, 2297b
	b 2296f
2295:
2296:
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
	bne %cr0, 2291b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2298:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2298b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r5, 0
	rldicl %r17, %r11, 63, 1
2299:
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
	bne %cr0, 2299b
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
2300:
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
	bne %cr0, 2300b
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
2301:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2301b
	addi %r14, %r10, 0
	rldicl %r17, %r11, 63, 1
	li %r6, 0
	li %r4, 1
2302:
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
	bne %cr0, 2302b
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
2303:
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
	bne %cr0, 2303b
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
2304:
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
	bne %cr0, 2304b
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
2305:
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
	bne %cr0, 2305b
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
2306:
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
	bne %cr0, 2306b
	rldicl %r6, %r5, 63, 1
	xor %r6, %r6, %r5
	and %r6, %r6, %r9
	xor %r6, %r6, %r5
	std %r6, 0(%r16)
	li %r3, 0
	std %r3, 176(%r31)
	li %r3, 4
	std %r3, 160(%r31)
2307:
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
	beq %cr0, 2308f
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
2310:
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2310b
	add %r15, %r10, %r6
	addi %r15, %r15, -1
	addi %r16, %r12, 0
	addi %r17, %r6, 0
2311:
	lbz %r0, 0(%r16)
	stb %r0, 0(%r15)
	addi %r16, %r16, 1
	addi %r15, %r15, -1
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2311b
	addi %r10, %r31, 256
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	addi %r5, %r5, -8
	ld %r4, 192(%r31)
	ld %r6, 0(%r5)
	and %r6, %r6, %r4
	std %r6, 0(%r5)
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r24, 0(%r5)
	rldicl %r24, %r24, 63, 1
	addi %r5, %r5, 8
	rldicl %r6, %r11, 63, 1
	addi %r6, %r6, -1
2312:
	ld %r3, 0(%r5)
	or %r24, %r24, %r3
	addi %r5, %r5, 8
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 2312b
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
2313:
	ld %r0, 0(%r15)
	std %r0, 0(%r14)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2313b
	addi %r5, %r10, 0
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	add %r5, %r5, %r29
	ld %r3, 0(%r5)
	li %r4, 1
	or %r3, %r3, %r4
	std %r3, 0(%r5)
	rldicr %r6, %r11, 2, 61
	add %r5, %r5, %r6
	li %r0, 0
	std %r0, 0(%r5)
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
2314:
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
	bne %cr0, 2314b
	lwz %r0, 0(%r14)
	subf %r0, %r20, %r0
	rldicl %r0, %r0, 1, 63
	li %r3, 0
	subf %r20, %r0, %r3
	cmpldi %cr0, %r24, 0
	beq %cr0, 2315f
	cmpldi %cr0, %r20, 0
	beq %cr0, 2317f
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
2319:
	std %r22, 0(%r14)
	addi %r14, %r14, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2319b
2320:
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
	beq %cr0, 2321f
2323:
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
	bne %cr0, 2323b
	b 2322f
2321:
2322:
	rldicl %r16, %r11, 63, 1
	addi %r16, %r16, -1
	rldicl %r16, %r16, 62, 2
	cmpldi %cr0, %r16, 0
	beq %cr0, 2324f
2326:
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
	bne %cr0, 2326b
	b 2325f
2324:
2325:
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
	bne %cr0, 2320b
	addi %r14, %r8, 0
	addi %r15, %r9, 0
	addi %r16, %r10, 0
	rldicl %r17, %r11, 63, 1
	subfc %r0, %r0, %r0
2327:
	ld %r0, 0(%r14)
	ld %r3, 0(%r16)
	subfe %r0, %r3, %r0
	std %r0, 0(%r15)
	addi %r14, %r14, 8
	addi %r15, %r15, 8
	addi %r16, %r16, 8
	addi %r17, %r17, -1
	cmpldi %cr0, %r17, 0
	bne %cr0, 2327b
	ld %r0, 0(%r14)
	li %r3, 0
	subfe %r0, %r3, %r0
	subfe %r20, %r20, %r20
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
	beq %cr0, 2329f
	ld %r3, 176(%r31)
	ld %r4, 168(%r31)
	addi %r3, %r3, 1
	std %r3, 176(%r31)
	subf %r4, %r3, %r4
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 3
	mulld %r4, %r4, %r5
	li %r5, 4
	subf %r4, %r4, %r5
	std %r4, 160(%r31)
	b 2330f
2329:
	li %r3, 2
	std %r3, 160(%r31)
2330:
	b 2318f
2317:
2318:
	b 2316f
2315:
2316:
	b 2309f
2308:
	li %r3, 0
	std %r3, 160(%r31)
2309:
	ld %r3, 160(%r31)
	addi %r3, %r3, -4
	cmpldi %cr0, %r3, 0
	beq %cr0, 2307b
	ld %r3, 160(%r31)
	cmpldi %cr0, %r3, 0
	beq %cr0, 2331f
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	beq %cr0, 2333f
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 2
	b 2334f
2333:
	ld %r4, 16(%r31)
	ld %r5, 24(%r31)
	add %r6, %r10, %r5
	addi %r6, %r6, -1
2335:
	lbz %r0, 0(%r6)
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r6, %r6, -1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 2335b
	ld %r4, 32(%r31)
	ld %r5, 152(%r31)
	std %r5, 0(%r4)
	li %r3, 1
2334:
	b 2332f
2331:
	ld %r4, 32(%r31)
	li %r5, 0
	std %r5, 0(%r4)
	li %r3, 0
2332:
2278:
2228:
213:
	b 22f
21:
	ld %r4, 32(%r31)
	li %r5, 0
	std %r5, 0(%r4)
	li %r3, 0
22:
	ld %r11, 0(%r31)
	rldicr %r11, %r11, 3, 60
	add %r11, %r31, %r11
	addi %r11, %r11, -160
	ld %r0, 144(%r11)
	mtlr %r0
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
