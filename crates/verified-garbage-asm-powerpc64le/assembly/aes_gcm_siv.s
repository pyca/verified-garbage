// The functions of `src/aes_gcm_siv.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_siv_seal:
	stdu %r1, -3936(%r1)
	addi %r12, %r1, 0
	addi %r0, %r12, 104
	std %r0, 96(%r12)
	addi %r12, %r1, 0
	ld %r11, 96(%r12)
	mflr %r0
	std %r15, 136(%r11)
	std %r16, 144(%r11)
	std %r17, 152(%r11)
	std %r18, 160(%r11)
	std %r19, 168(%r11)
	std %r20, 176(%r11)
	std %r21, 184(%r11)
	std %r22, 192(%r11)
	std %r23, 200(%r11)
	std %r24, 208(%r11)
	std %r25, 216(%r11)
	std %r14, 128(%r11)
	std %r0, 224(%r11)
	or %r14, %r11, %r11
	or %r15, %r5, %r5
	or %r16, %r3, %r3
	or %r17, %r4, %r4
	or %r18, %r6, %r6
	or %r19, %r7, %r7
	or %r20, %r8, %r8
	or %r21, %r9, %r9
	or %r22, %r10, %r10
	li %r25, 0
	addi %r4, %r14, 496
	rldicl %r5, %r17, 63, 1
	addi %r5, %r5, -1
20:
	lwz %r3, 0(%r15)
	lwz %r6, 4(%r15)
	lwz %r7, 8(%r15)
	stw %r25, 0(%r4)
	stw %r3, 4(%r4)
	stw %r6, 8(%r4)
	stw %r7, 12(%r4)
	addi %r25, %r25, 1
	addi %r4, %r4, 16
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1776
	bl {vg_aes_encrypt_blocks}
	addi %r5, %r14, 496
	addi %r4, %r14, 16
21:
	ld %r3, 0(%r5)
	std %r3, 0(%r4)
	addi %r5, %r5, 16
	addi %r4, %r4, 8
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 21b
	addi %r3, %r14, 32
	addi %r4, %r17, -6
	rldicr %r4, %r4, 2, 61
	addi %r5, %r14, 256
	addi %r6, %r14, 1776
	bl {vg_aes_expand_key_scratch}
	ld %r3, 16(%r14)
	ld %r4, 24(%r14)
	li %r5, 1
	and %r5, %r3, %r5
	li %r6, 0
	subf %r5, %r5, %r6
	rldicl %r3, %r3, 63, 1
	rldicr %r6, %r4, 63, 0
	or %r3, %r3, %r6
	rldicl %r4, %r4, 63, 1
	lis %r6, -7936
	rldicr %r6, %r6, 32, 31
	and %r5, %r5, %r6
	xor %r4, %r4, %r5
	li %r7, 64
	stdbrx %r4, %r14, %r7
	li %r7, 72
	stdbrx %r3, %r14, %r7
	li %r0, 0
	std %r0, 80(%r14)
	std %r0, 88(%r14)
	or %r23, %r18, %r18
	or %r24, %r19, %r19
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	beq %cr0, 22f
24:
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 25f
	li %r25, 64
	b 26f
25:
	rldicl %r25, %r24, 60, 4
26:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
27:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 27b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	b 23f
22:
23:
	cmpldi %cr0, %r24, 0
	beq %cr0, 28f
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	or %r3, %r23, %r23
	addi %r4, %r14, 240
	or %r5, %r24, %r24
210:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	addi %r23, %r14, 240
	li %r24, 16
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 211f
	li %r25, 64
	b 212f
211:
	rldicl %r25, %r24, 60, 4
212:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
213:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 213b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	b 29f
28:
29:
	or %r23, %r20, %r20
	or %r24, %r21, %r21
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	beq %cr0, 214f
216:
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 217f
	li %r25, 64
	b 218f
217:
	rldicl %r25, %r24, 60, 4
218:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
219:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 219b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	bne %cr0, 216b
	b 215f
214:
215:
	cmpldi %cr0, %r24, 0
	beq %cr0, 220f
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	or %r3, %r23, %r23
	addi %r4, %r14, 240
	or %r5, %r24, %r24
222:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 222b
	addi %r23, %r14, 240
	li %r24, 16
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 223f
	li %r25, 64
	b 224f
223:
	rldicl %r25, %r24, 60, 4
224:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
225:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 225b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	b 221f
220:
221:
	rldicr %r3, %r19, 3, 60
	std %r3, 240(%r14)
	rldicr %r3, %r21, 3, 60
	std %r3, 248(%r14)
	addi %r23, %r14, 240
	li %r24, 16
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 226f
	li %r25, 64
	b 227f
226:
	rldicl %r25, %r24, 60, 4
227:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
228:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 228b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	li %r9, 88
	ldbrx %r3, %r14, %r9
	li %r9, 80
	ldbrx %r4, %r14, %r9
	ld %r5, 0(%r15)
	xor %r3, %r3, %r5
	lwz %r5, 8(%r15)
	xor %r4, %r4, %r5
	rldicr %r4, %r4, 1, 62
	rldicl %r4, %r4, 63, 1
	std %r3, 96(%r14)
	std %r4, 104(%r14)
	ld %r3, 96(%r14)
	ld %r4, 104(%r14)
	std %r3, 112(%r14)
	std %r4, 120(%r14)
	li %r0, 0
	std %r0, 0(%r14)
	std %r0, 8(%r14)
	addi %r3, %r14, 256
	or %r4, %r17, %r17
	addi %r5, %r14, 112
	addi %r8, %r14, 1776
	addi %r6, %r14, 0
	li %r7, 1
	bl {vg_aes_ctr32}
	or %r23, %r20, %r20
	or %r24, %r21, %r21
	ld %r3, 0(%r14)
	ld %r4, 8(%r14)
	li %r5, 1
	rldicr %r5, %r5, 63, 0
	or %r4, %r4, %r5
	std %r3, 96(%r14)
	std %r4, 104(%r14)
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	beq %cr0, 229f
231:
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 232f
	li %r25, 64
	b 233f
232:
	rldicl %r25, %r24, 60, 4
233:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
234:
	ld %r5, 96(%r14)
	ld %r6, 104(%r14)
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	lwz %r5, 96(%r14)
	addi %r5, %r5, 1
	stw %r5, 96(%r14)
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 234b
	addi %r3, %r14, 256
	or %r4, %r17, %r17
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1776
	bl {vg_aes_encrypt_blocks}
	addi %r3, %r14, 496
	or %r4, %r23, %r23
	rldicr %r5, %r25, 1, 62
235:
	ld %r0, 0(%r4)
	ld %r6, 0(%r3)
	xor %r0, %r0, %r6
	std %r0, 0(%r4)
	addi %r3, %r3, 8
	addi %r4, %r4, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 235b
	or %r23, %r4, %r4
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	bne %cr0, 231b
	b 230f
229:
230:
	cmpldi %cr0, %r24, 0
	beq %cr0, 236f
	ld %r3, 96(%r14)
	ld %r4, 104(%r14)
	std %r3, 112(%r14)
	std %r4, 120(%r14)
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	addi %r3, %r14, 256
	or %r4, %r17, %r17
	addi %r5, %r14, 112
	addi %r8, %r14, 1776
	addi %r6, %r14, 240
	li %r7, 1
	bl {vg_aes_ctr32}
	addi %r3, %r14, 240
	or %r4, %r23, %r23
	or %r5, %r24, %r24
238:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 238b
	b 237f
236:
237:
	ld %r3, 0(%r14)
	ld %r4, 8(%r14)
	std %r3, 0(%r22)
	std %r4, 8(%r22)
	ld %r0, 224(%r14)
	mtlr %r0
	ld %r15, 136(%r14)
	ld %r16, 144(%r14)
	ld %r17, 152(%r14)
	ld %r18, 160(%r14)
	ld %r19, 168(%r14)
	ld %r20, 176(%r14)
	ld %r21, 184(%r14)
	ld %r22, 192(%r14)
	ld %r23, 200(%r14)
	ld %r24, 208(%r14)
	ld %r25, 216(%r14)
	ld %r14, 128(%r14)
	addi %r1, %r1, 3936
	blr

vg_aes_gcm_siv_open:
	stdu %r1, -3936(%r1)
	addi %r12, %r1, 0
	addi %r0, %r12, 104
	std %r0, 96(%r12)
	addi %r12, %r1, 0
	ld %r11, 96(%r12)
	mflr %r0
	std %r15, 136(%r11)
	std %r16, 144(%r11)
	std %r17, 152(%r11)
	std %r18, 160(%r11)
	std %r19, 168(%r11)
	std %r20, 176(%r11)
	std %r21, 184(%r11)
	std %r22, 192(%r11)
	std %r23, 200(%r11)
	std %r24, 208(%r11)
	std %r25, 216(%r11)
	std %r14, 128(%r11)
	std %r0, 224(%r11)
	or %r14, %r11, %r11
	or %r15, %r5, %r5
	or %r16, %r3, %r3
	or %r17, %r4, %r4
	or %r18, %r6, %r6
	or %r19, %r7, %r7
	or %r20, %r8, %r8
	or %r21, %r9, %r9
	or %r22, %r10, %r10
	ld %r3, 0(%r22)
	ld %r4, 8(%r22)
	std %r3, 0(%r14)
	std %r4, 8(%r14)
	li %r25, 0
	addi %r4, %r14, 496
	rldicl %r5, %r17, 63, 1
	addi %r5, %r5, -1
20:
	lwz %r3, 0(%r15)
	lwz %r6, 4(%r15)
	lwz %r7, 8(%r15)
	stw %r25, 0(%r4)
	stw %r3, 4(%r4)
	stw %r6, 8(%r4)
	stw %r7, 12(%r4)
	addi %r25, %r25, 1
	addi %r4, %r4, 16
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1776
	bl {vg_aes_encrypt_blocks}
	addi %r5, %r14, 496
	addi %r4, %r14, 16
21:
	ld %r3, 0(%r5)
	std %r3, 0(%r4)
	addi %r5, %r5, 16
	addi %r4, %r4, 8
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 21b
	addi %r3, %r14, 32
	addi %r4, %r17, -6
	rldicr %r4, %r4, 2, 61
	addi %r5, %r14, 256
	addi %r6, %r14, 1776
	bl {vg_aes_expand_key_scratch}
	ld %r3, 16(%r14)
	ld %r4, 24(%r14)
	li %r5, 1
	and %r5, %r3, %r5
	li %r6, 0
	subf %r5, %r5, %r6
	rldicl %r3, %r3, 63, 1
	rldicr %r6, %r4, 63, 0
	or %r3, %r3, %r6
	rldicl %r4, %r4, 63, 1
	lis %r6, -7936
	rldicr %r6, %r6, 32, 31
	and %r5, %r5, %r6
	xor %r4, %r4, %r5
	li %r7, 64
	stdbrx %r4, %r14, %r7
	li %r7, 72
	stdbrx %r3, %r14, %r7
	li %r0, 0
	std %r0, 80(%r14)
	std %r0, 88(%r14)
	or %r23, %r20, %r20
	or %r24, %r21, %r21
	ld %r3, 0(%r14)
	ld %r4, 8(%r14)
	li %r5, 1
	rldicr %r5, %r5, 63, 0
	or %r4, %r4, %r5
	std %r3, 96(%r14)
	std %r4, 104(%r14)
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	beq %cr0, 22f
24:
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 25f
	li %r25, 64
	b 26f
25:
	rldicl %r25, %r24, 60, 4
26:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
27:
	ld %r5, 96(%r14)
	ld %r6, 104(%r14)
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	lwz %r5, 96(%r14)
	addi %r5, %r5, 1
	stw %r5, 96(%r14)
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 27b
	addi %r3, %r14, 256
	or %r4, %r17, %r17
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1776
	bl {vg_aes_encrypt_blocks}
	addi %r3, %r14, 496
	or %r4, %r23, %r23
	rldicr %r5, %r25, 1, 62
28:
	ld %r0, 0(%r4)
	ld %r6, 0(%r3)
	xor %r0, %r0, %r6
	std %r0, 0(%r4)
	addi %r3, %r3, 8
	addi %r4, %r4, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	or %r23, %r4, %r4
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	bne %cr0, 24b
	b 23f
22:
23:
	cmpldi %cr0, %r24, 0
	beq %cr0, 29f
	ld %r3, 96(%r14)
	ld %r4, 104(%r14)
	std %r3, 112(%r14)
	std %r4, 120(%r14)
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	addi %r3, %r14, 256
	or %r4, %r17, %r17
	addi %r5, %r14, 112
	addi %r8, %r14, 1776
	addi %r6, %r14, 240
	li %r7, 1
	bl {vg_aes_ctr32}
	addi %r3, %r14, 240
	or %r4, %r23, %r23
	or %r5, %r24, %r24
211:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 211b
	b 210f
29:
210:
	or %r23, %r18, %r18
	or %r24, %r19, %r19
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	beq %cr0, 212f
214:
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 215f
	li %r25, 64
	b 216f
215:
	rldicl %r25, %r24, 60, 4
216:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
217:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 217b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	bne %cr0, 214b
	b 213f
212:
213:
	cmpldi %cr0, %r24, 0
	beq %cr0, 218f
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	or %r3, %r23, %r23
	addi %r4, %r14, 240
	or %r5, %r24, %r24
220:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
	addi %r23, %r14, 240
	li %r24, 16
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 221f
	li %r25, 64
	b 222f
221:
	rldicl %r25, %r24, 60, 4
222:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
223:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 223b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	b 219f
218:
219:
	or %r23, %r20, %r20
	or %r24, %r21, %r21
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	beq %cr0, 224f
226:
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 227f
	li %r25, 64
	b 228f
227:
	rldicl %r25, %r24, 60, 4
228:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
229:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 229b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	bne %cr0, 226b
	b 225f
224:
225:
	cmpldi %cr0, %r24, 0
	beq %cr0, 230f
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	or %r3, %r23, %r23
	addi %r4, %r14, 240
	or %r5, %r24, %r24
232:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 232b
	addi %r23, %r14, 240
	li %r24, 16
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 233f
	li %r25, 64
	b 234f
233:
	rldicl %r25, %r24, 60, 4
234:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
235:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 235b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	b 231f
230:
231:
	rldicr %r3, %r19, 3, 60
	std %r3, 240(%r14)
	rldicr %r3, %r21, 3, 60
	std %r3, 248(%r14)
	addi %r23, %r14, 240
	li %r24, 16
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 236f
	li %r25, 64
	b 237f
236:
	rldicl %r25, %r24, 60, 4
237:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
238:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 238b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	li %r9, 88
	ldbrx %r3, %r14, %r9
	li %r9, 80
	ldbrx %r4, %r14, %r9
	ld %r5, 0(%r15)
	xor %r3, %r3, %r5
	lwz %r5, 8(%r15)
	xor %r4, %r4, %r5
	rldicr %r4, %r4, 1, 62
	rldicl %r4, %r4, 63, 1
	std %r3, 96(%r14)
	std %r4, 104(%r14)
	ld %r3, 96(%r14)
	ld %r4, 104(%r14)
	std %r3, 112(%r14)
	std %r4, 120(%r14)
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	addi %r3, %r14, 256
	or %r4, %r17, %r17
	addi %r5, %r14, 112
	addi %r8, %r14, 1776
	addi %r6, %r14, 240
	li %r7, 1
	bl {vg_aes_ctr32}
	ld %r3, 0(%r14)
	ld %r4, 240(%r14)
	xor %r3, %r3, %r4
	ld %r4, 8(%r14)
	ld %r5, 248(%r14)
	xor %r4, %r4, %r5
	or %r3, %r3, %r4
	li %r4, 0
	subf %r4, %r3, %r4
	or %r3, %r3, %r4
	rldicl %r3, %r3, 1, 63
	li %r25, 1
	subf %r25, %r3, %r25
	li %r9, 0
	subf %r9, %r25, %r9
	or %r3, %r20, %r20
	rldicl %r4, %r21, 61, 3
	rldicr %r5, %r4, 3, 60
	subf %r5, %r5, %r21
	cmpldi %cr0, %r4, 0
	beq %cr0, 239f
241:
	ld %r0, 0(%r3)
	and %r0, %r0, %r9
	std %r0, 0(%r3)
	addi %r3, %r3, 8
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 241b
	b 240f
239:
240:
	cmpldi %cr0, %r5, 0
	beq %cr0, 242f
244:
	lbz %r0, 0(%r3)
	and %r0, %r0, %r9
	stb %r0, 0(%r3)
	addi %r3, %r3, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 244b
	b 243f
242:
243:
	or %r3, %r25, %r25
	ld %r0, 224(%r14)
	mtlr %r0
	ld %r15, 136(%r14)
	ld %r16, 144(%r14)
	ld %r17, 152(%r14)
	ld %r18, 160(%r14)
	ld %r19, 168(%r14)
	ld %r20, 176(%r14)
	ld %r21, 184(%r14)
	ld %r22, 192(%r14)
	ld %r23, 200(%r14)
	ld %r24, 208(%r14)
	ld %r25, 216(%r14)
	ld %r14, 128(%r14)
	addi %r1, %r1, 3936
	blr
