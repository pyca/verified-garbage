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
20:
	lwz %r3, 0(%r15)
	lwz %r4, 4(%r15)
	lwz %r5, 8(%r15)
	stw %r25, 112(%r14)
	stw %r3, 116(%r14)
	stw %r4, 120(%r14)
	stw %r5, 124(%r14)
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 112
	addi %r6, %r14, 240
	li %r7, 1
	addi %r8, %r14, 1776
	bl {vg_aes_ctr32}
	ld %r3, 240(%r14)
	rldicr %r4, %r25, 3, 60
	add %r4, %r14, %r4
	std %r3, 16(%r4)
	addi %r25, %r25, 1
	rldicl %r5, %r17, 63, 1
	addi %r5, %r5, -1
	subf %r5, %r25, %r5
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
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
	beq %cr0, 21f
23:
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 24f
	li %r25, 64
	b 25f
24:
	rldicl %r25, %r24, 60, 4
25:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
26:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 26b
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
	bne %cr0, 23b
	b 22f
21:
22:
	cmpldi %cr0, %r24, 0
	beq %cr0, 27f
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	or %r3, %r23, %r23
	addi %r4, %r14, 240
	or %r5, %r24, %r24
29:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 29b
	addi %r23, %r14, 240
	li %r24, 16
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 210f
	li %r25, 64
	b 211f
210:
	rldicl %r25, %r24, 60, 4
211:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
212:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 212b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	b 28f
27:
28:
	or %r23, %r20, %r20
	or %r24, %r21, %r21
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	beq %cr0, 213f
215:
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 216f
	li %r25, 64
	b 217f
216:
	rldicl %r25, %r24, 60, 4
217:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
218:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 218b
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
	bne %cr0, 215b
	b 214f
213:
214:
	cmpldi %cr0, %r24, 0
	beq %cr0, 219f
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	or %r3, %r23, %r23
	addi %r4, %r14, 240
	or %r5, %r24, %r24
221:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 221b
	addi %r23, %r14, 240
	li %r24, 16
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 222f
	li %r25, 64
	b 223f
222:
	rldicl %r25, %r24, 60, 4
223:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
224:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 224b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	b 220f
219:
220:
	rldicr %r3, %r19, 3, 60
	std %r3, 240(%r14)
	rldicr %r3, %r21, 3, 60
	std %r3, 248(%r14)
	addi %r23, %r14, 240
	li %r24, 16
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 225f
	li %r25, 64
	b 226f
225:
	rldicl %r25, %r24, 60, 4
226:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
227:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 227b
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
	beq %cr0, 228f
230:
	ld %r3, 96(%r14)
	ld %r4, 104(%r14)
	std %r3, 112(%r14)
	std %r4, 120(%r14)
	addi %r3, %r14, 256
	or %r4, %r17, %r17
	addi %r5, %r14, 112
	addi %r8, %r14, 1776
	or %r6, %r23, %r23
	li %r7, 1
	bl {vg_aes_ctr32}
	lwz %r3, 96(%r14)
	addi %r3, %r3, 1
	stw %r3, 96(%r14)
	addi %r23, %r23, 16
	addi %r24, %r24, -16
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	bne %cr0, 230b
	b 229f
228:
229:
	cmpldi %cr0, %r24, 0
	beq %cr0, 231f
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
233:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 233b
	b 232f
231:
232:
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
20:
	lwz %r3, 0(%r15)
	lwz %r4, 4(%r15)
	lwz %r5, 8(%r15)
	stw %r25, 112(%r14)
	stw %r3, 116(%r14)
	stw %r4, 120(%r14)
	stw %r5, 124(%r14)
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 112
	addi %r6, %r14, 240
	li %r7, 1
	addi %r8, %r14, 1776
	bl {vg_aes_ctr32}
	ld %r3, 240(%r14)
	rldicr %r4, %r25, 3, 60
	add %r4, %r14, %r4
	std %r3, 16(%r4)
	addi %r25, %r25, 1
	rldicl %r5, %r17, 63, 1
	addi %r5, %r5, -1
	subf %r5, %r25, %r5
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
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
	beq %cr0, 21f
23:
	ld %r3, 96(%r14)
	ld %r4, 104(%r14)
	std %r3, 112(%r14)
	std %r4, 120(%r14)
	addi %r3, %r14, 256
	or %r4, %r17, %r17
	addi %r5, %r14, 112
	addi %r8, %r14, 1776
	or %r6, %r23, %r23
	li %r7, 1
	bl {vg_aes_ctr32}
	lwz %r3, 96(%r14)
	addi %r3, %r3, 1
	stw %r3, 96(%r14)
	addi %r23, %r23, 16
	addi %r24, %r24, -16
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	bne %cr0, 23b
	b 22f
21:
22:
	cmpldi %cr0, %r24, 0
	beq %cr0, 24f
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
26:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 26b
	b 25f
24:
25:
	or %r23, %r18, %r18
	or %r24, %r19, %r19
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	beq %cr0, 27f
29:
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 210f
	li %r25, 64
	b 211f
210:
	rldicl %r25, %r24, 60, 4
211:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
212:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 212b
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
	bne %cr0, 29b
	b 28f
27:
28:
	cmpldi %cr0, %r24, 0
	beq %cr0, 213f
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	or %r3, %r23, %r23
	addi %r4, %r14, 240
	or %r5, %r24, %r24
215:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
	addi %r23, %r14, 240
	li %r24, 16
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 216f
	li %r25, 64
	b 217f
216:
	rldicl %r25, %r24, 60, 4
217:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
218:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 218b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	b 214f
213:
214:
	or %r23, %r20, %r20
	or %r24, %r21, %r21
	rldicl %r11, %r24, 60, 4
	cmpldi %cr0, %r11, 0
	beq %cr0, 219f
221:
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 222f
	li %r25, 64
	b 223f
222:
	rldicl %r25, %r24, 60, 4
223:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
224:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 224b
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
	bne %cr0, 221b
	b 220f
219:
220:
	cmpldi %cr0, %r24, 0
	beq %cr0, 225f
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	or %r3, %r23, %r23
	addi %r4, %r14, 240
	or %r5, %r24, %r24
227:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 227b
	addi %r23, %r14, 240
	li %r24, 16
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 228f
	li %r25, 64
	b 229f
228:
	rldicl %r25, %r24, 60, 4
229:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
230:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 230b
	rldicr %r5, %r25, 4, 59
	subf %r24, %r5, %r24
	addi %r3, %r14, 64
	addi %r4, %r14, 80
	addi %r5, %r14, 496
	or %r6, %r25, %r25
	addi %r7, %r14, 1520
	bl {vg_ghash}
	rldicl %r11, %r24, 60, 4
	b 226f
225:
226:
	rldicr %r3, %r19, 3, 60
	std %r3, 240(%r14)
	rldicr %r3, %r21, 3, 60
	std %r3, 248(%r14)
	addi %r23, %r14, 240
	li %r24, 16
	rldicl %r25, %r24, 54, 10
	cmpldi %cr0, %r25, 0
	beq %cr0, 231f
	li %r25, 64
	b 232f
231:
	rldicl %r25, %r24, 60, 4
232:
	addi %r4, %r14, 496
	or %r3, %r25, %r25
	li %r9, 8
	li %r10, 0
233:
	ldbrx %r5, %r23, %r9
	ldbrx %r6, %r23, %r10
	std %r5, 0(%r4)
	std %r6, 8(%r4)
	addi %r23, %r23, 16
	addi %r4, %r4, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 233b
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
	or %r4, %r21, %r21
	cmpldi %cr0, %r4, 0
	beq %cr0, 234f
236:
	lbz %r0, 0(%r3)
	and %r0, %r0, %r9
	stb %r0, 0(%r3)
	addi %r3, %r3, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 236b
	b 235f
234:
235:
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
