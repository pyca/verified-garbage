// The functions of `src/gcm.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_gcm_init:
	stdu %r1, -2592(%r1)
	addi %r6, %r1, 32
	std %r18, 128(%r6)
	std %r19, 136(%r6)
	std %r20, 144(%r6)
	std %r21, 152(%r6)
	std %r22, 160(%r6)
	std %r23, 168(%r6)
	std %r24, 176(%r6)
	std %r25, 184(%r6)
	std %r26, 192(%r6)
	std %r27, 200(%r6)
	std %r28, 208(%r6)
	std %r29, 216(%r6)
	std %r30, 224(%r6)
	std %r31, 232(%r6)
	mflr %r0
	std %r0, 240(%r6)
	or %r31, %r6, %r6
	or %r29, %r5, %r5
	rldicl %r28, %r4, 62, 2
	addi %r28, %r28, 6
	addi %r6, %r31, 512
	bl {vg_aes_expand_key_scratch}
	li %r0, 0
	std %r0, 240(%r29)
	std %r0, 248(%r29)
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r31, 96
	addi %r6, %r29, 240
	li %r7, 1
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 2592
	blr

vg_aes_gcm_stream_init:
	stdu %r1, -2592(%r1)
	addi %r7, %r1, 32
	std %r18, 128(%r7)
	std %r19, 136(%r7)
	std %r20, 144(%r7)
	std %r21, 152(%r7)
	std %r22, 160(%r7)
	std %r23, 168(%r7)
	std %r24, 176(%r7)
	std %r25, 184(%r7)
	std %r26, 192(%r7)
	std %r27, 200(%r7)
	std %r28, 208(%r7)
	std %r29, 216(%r7)
	std %r30, 224(%r7)
	std %r31, 232(%r7)
	mflr %r0
	std %r0, 240(%r7)
	or %r31, %r7, %r7
	or %r30, %r6, %r6
	or %r29, %r3, %r3
	or %r24, %r4, %r4
	or %r25, %r5, %r5
	or %r18, %r5, %r5
	addi %r6, %r25, -12
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
	li %r0, 0
	std %r0, 0(%r30)
	std %r0, 8(%r30)
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 22f
	cmpldi %cr0, %r26, 0
	beq %cr0, 24f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 26f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 28f
	b 29f
28:
	or %r5, %r25, %r25
29:
	b 27f
26:
27:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
210:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 211f
	b 212f
211:
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
212:
	b 25f
24:
25:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 213f
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 214f
213:
214:
	cmpldi %cr0, %r25, 0
	beq %cr0, 215f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
217:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 217b
	b 216f
215:
216:
	b 23f
22:
23:
	li %r0, 15
	and %r26, %r18, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 218f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
220:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 219f
218:
219:
	li %r24, 0
	or %r26, %r18, %r18
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 21f
20:
	lwz %r3, 0(%r24)
	lwz %r4, 4(%r24)
	lwz %r5, 8(%r24)
	lis %r6, 256
	stw %r3, 0(%r30)
	stw %r4, 4(%r30)
	stw %r5, 8(%r30)
	stw %r6, 12(%r30)
21:
	lwz %r3, 0(%r30)
	lwz %r4, 4(%r30)
	lwz %r5, 8(%r30)
	addi %r7, %r30, 12
	li %r8, 0
	lwbrx %r6, %r7, %r8
	addi %r6, %r6, 1
	stw %r3, 48(%r30)
	stw %r4, 52(%r30)
	stw %r5, 56(%r30)
	addi %r7, %r30, 60
	stwbrx %r6, %r7, %r8
	std %r8, 16(%r30)
	std %r8, 24(%r30)
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 2592
	blr

vg_aes_gcm_stream_aad:
	stdu %r1, -2592(%r1)
	addi %r8, %r1, 32
	std %r18, 128(%r8)
	std %r19, 136(%r8)
	std %r20, 144(%r8)
	std %r21, 152(%r8)
	std %r22, 160(%r8)
	std %r23, 168(%r8)
	std %r24, 176(%r8)
	std %r25, 184(%r8)
	std %r26, 192(%r8)
	std %r27, 200(%r8)
	std %r28, 208(%r8)
	std %r29, 216(%r8)
	std %r30, 224(%r8)
	std %r31, 232(%r8)
	mflr %r0
	std %r0, 240(%r8)
	or %r31, %r8, %r8
	or %r30, %r4, %r4
	or %r29, %r3, %r3
	or %r24, %r6, %r6
	or %r25, %r7, %r7
	li %r0, 15
	and %r26, %r5, %r0
	cmpldi %cr0, %r25, 0
	beq %cr0, 20f
	cmpldi %cr0, %r26, 0
	beq %cr0, 22f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 24f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 26f
	b 27f
26:
	or %r5, %r25, %r25
27:
	b 25f
24:
25:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
28:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 29f
	b 210f
29:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
210:
	b 23f
22:
23:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 211f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 212f
211:
212:
	cmpldi %cr0, %r25, 0
	beq %cr0, 213f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
215:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
	b 214f
213:
214:
	b 21f
20:
21:
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 2592
	blr

vg_aes_gcm_stream_encrypt:
	stdu %r1, -2592(%r1)
	addi %r10, %r1, 32
	std %r18, 128(%r10)
	std %r19, 136(%r10)
	std %r20, 144(%r10)
	std %r21, 152(%r10)
	std %r22, 160(%r10)
	std %r23, 168(%r10)
	std %r24, 176(%r10)
	std %r25, 184(%r10)
	std %r26, 192(%r10)
	std %r27, 200(%r10)
	std %r28, 208(%r10)
	std %r29, 216(%r10)
	std %r30, 224(%r10)
	std %r31, 232(%r10)
	mflr %r0
	std %r0, 240(%r10)
	or %r31, %r10, %r10
	or %r30, %r5, %r5
	or %r29, %r3, %r3
	or %r28, %r4, %r4
	or %r22, %r6, %r6
	or %r23, %r7, %r7
	or %r20, %r8, %r8
	or %r19, %r9, %r9
	or %r24, %r20, %r20
	or %r25, %r19, %r19
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r25, 0
	beq %cr0, 20f
	cmpldi %cr0, %r26, 0
	beq %cr0, 22f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 24f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 26f
	b 27f
26:
	or %r5, %r25, %r25
27:
	b 25f
24:
25:
	addi %r3, %r30, 64
	add %r3, %r3, %r26
	or %r4, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
28:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	b 23f
22:
23:
	or %r6, %r24, %r24
	rldicl %r7, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r7, 0
	beq %cr0, 29f
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	b 210f
29:
210:
	cmpldi %cr0, %r25, 0
	beq %cr0, 211f
	li %r0, 0
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	addi %r6, %r30, 64
	li %r7, 1
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	addi %r3, %r30, 64
	or %r4, %r24, %r24
	or %r5, %r25, %r25
213:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 213b
	b 212f
211:
212:
	b 21f
20:
21:
	cmpldi %cr0, %r19, 0
	beq %cr0, 214f
	cmpldi %cr0, %r23, 0
	beq %cr0, 216f
	b 217f
216:
	li %r0, 15
	and %r26, %r22, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 218f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
220:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 219f
218:
219:
217:
	or %r24, %r20, %r20
	or %r25, %r19, %r19
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r25, 0
	beq %cr0, 221f
	cmpldi %cr0, %r26, 0
	beq %cr0, 223f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 225f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 227f
	b 228f
227:
	or %r5, %r25, %r25
228:
	b 226f
225:
226:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
229:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 229b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 230f
	b 231f
230:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
231:
	b 224f
223:
224:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 232f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 233f
232:
233:
	cmpldi %cr0, %r25, 0
	beq %cr0, 234f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
236:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 236b
	b 235f
234:
235:
	b 222f
221:
222:
	b 215f
214:
215:
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 2592
	blr

vg_aes_gcm_stream_decrypt:
	stdu %r1, -2592(%r1)
	addi %r10, %r1, 32
	std %r18, 128(%r10)
	std %r19, 136(%r10)
	std %r20, 144(%r10)
	std %r21, 152(%r10)
	std %r22, 160(%r10)
	std %r23, 168(%r10)
	std %r24, 176(%r10)
	std %r25, 184(%r10)
	std %r26, 192(%r10)
	std %r27, 200(%r10)
	std %r28, 208(%r10)
	std %r29, 216(%r10)
	std %r30, 224(%r10)
	std %r31, 232(%r10)
	mflr %r0
	std %r0, 240(%r10)
	or %r31, %r10, %r10
	or %r30, %r5, %r5
	or %r29, %r3, %r3
	or %r28, %r4, %r4
	or %r22, %r6, %r6
	or %r23, %r7, %r7
	or %r20, %r8, %r8
	or %r19, %r9, %r9
	cmpldi %cr0, %r19, 0
	beq %cr0, 20f
	cmpldi %cr0, %r23, 0
	beq %cr0, 22f
	b 23f
22:
	li %r0, 15
	and %r26, %r22, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 24f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
26:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 26b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 25f
24:
25:
23:
	or %r24, %r20, %r20
	or %r25, %r19, %r19
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r25, 0
	beq %cr0, 27f
	cmpldi %cr0, %r26, 0
	beq %cr0, 29f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 211f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 213f
	b 214f
213:
	or %r5, %r25, %r25
214:
	b 212f
211:
212:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
215:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 216f
	b 217f
216:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
217:
	b 210f
29:
210:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 218f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 219f
218:
219:
	cmpldi %cr0, %r25, 0
	beq %cr0, 220f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
222:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 222b
	b 221f
220:
221:
	b 28f
27:
28:
	b 21f
20:
21:
	or %r24, %r20, %r20
	or %r25, %r19, %r19
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r25, 0
	beq %cr0, 223f
	cmpldi %cr0, %r26, 0
	beq %cr0, 225f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 227f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 229f
	b 230f
229:
	or %r5, %r25, %r25
230:
	b 228f
227:
228:
	addi %r3, %r30, 64
	add %r3, %r3, %r26
	or %r4, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
231:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 231b
	b 226f
225:
226:
	or %r6, %r24, %r24
	rldicl %r7, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r7, 0
	beq %cr0, 232f
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	b 233f
232:
233:
	cmpldi %cr0, %r25, 0
	beq %cr0, 234f
	li %r0, 0
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	addi %r6, %r30, 64
	li %r7, 1
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	addi %r3, %r30, 64
	or %r4, %r24, %r24
	or %r5, %r25, %r25
236:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 236b
	b 235f
234:
235:
	b 224f
223:
224:
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 2592
	blr

vg_aes_gcm_stream_finish:
	stdu %r1, -2592(%r1)
	addi %r9, %r1, 32
	std %r18, 128(%r9)
	std %r19, 136(%r9)
	std %r20, 144(%r9)
	std %r21, 152(%r9)
	std %r22, 160(%r9)
	std %r23, 168(%r9)
	std %r24, 176(%r9)
	std %r25, 184(%r9)
	std %r26, 192(%r9)
	std %r27, 200(%r9)
	std %r28, 208(%r9)
	std %r29, 216(%r9)
	std %r30, 224(%r9)
	std %r31, 232(%r9)
	mflr %r0
	std %r0, 240(%r9)
	or %r31, %r9, %r9
	or %r30, %r5, %r5
	or %r29, %r3, %r3
	or %r28, %r4, %r4
	or %r22, %r6, %r6
	or %r23, %r7, %r7
	or %r20, %r8, %r8
	cmpldi %cr0, %r23, 0
	beq %cr0, 20f
	li %r0, 15
	and %r26, %r23, %r0
	b 21f
20:
	li %r0, 15
	and %r26, %r22, %r0
21:
	cmpldi %cr0, %r26, 0
	beq %cr0, 22f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
24:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 24b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 23f
22:
23:
	or %r24, %r22, %r22
	or %r26, %r23, %r23
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	ld %r3, 16(%r30)
	std %r3, 0(%r31)
	ld %r3, 24(%r30)
	std %r3, 8(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	or %r5, %r30, %r30
	addi %r6, %r31, 0
	li %r7, 1
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	ld %r3, 0(%r31)
	std %r3, 0(%r20)
	ld %r3, 8(%r31)
	std %r3, 8(%r20)
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 2592
	blr

vg_aes_gcm_stream_verify:
	stdu %r1, -2592(%r1)
	addi %r10, %r1, 32
	std %r18, 128(%r10)
	std %r19, 136(%r10)
	std %r20, 144(%r10)
	std %r21, 152(%r10)
	std %r22, 160(%r10)
	std %r23, 168(%r10)
	std %r24, 176(%r10)
	std %r25, 184(%r10)
	std %r26, 192(%r10)
	std %r27, 200(%r10)
	std %r28, 208(%r10)
	std %r29, 216(%r10)
	std %r30, 224(%r10)
	std %r31, 232(%r10)
	mflr %r0
	std %r0, 240(%r10)
	or %r31, %r10, %r10
	or %r30, %r5, %r5
	or %r29, %r3, %r3
	or %r28, %r4, %r4
	or %r22, %r6, %r6
	or %r23, %r7, %r7
	or %r20, %r8, %r8
	or %r19, %r9, %r9
	li %r25, 0
	rldicl %r0, %r19, 62, 2
	cmpldi %cr0, %r0, 0
	beq %cr0, 20f
	rldicl %r0, %r19, 60, 4
	cmpldi %cr0, %r0, 0
	beq %cr0, 22f
	addi %r0, %r19, -16
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	b 25f
24:
	li %r25, 1
25:
	b 23f
22:
	li %r25, 1
23:
	b 21f
20:
21:
	cmpldi %cr0, %r25, 0
	beq %cr0, 26f
	li %r0, 0
	std %r0, 256(%r31)
	std %r0, 264(%r31)
	or %r3, %r20, %r20
	addi %r4, %r31, 256
	or %r5, %r19, %r19
28:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	cmpldi %cr0, %r23, 0
	beq %cr0, 29f
	li %r0, 15
	and %r26, %r23, %r0
	b 210f
29:
	li %r0, 15
	and %r26, %r22, %r0
210:
	cmpldi %cr0, %r26, 0
	beq %cr0, 211f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
213:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 213b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 212f
211:
212:
	or %r24, %r22, %r22
	or %r26, %r23, %r23
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	ld %r3, 16(%r30)
	std %r3, 0(%r31)
	ld %r3, 24(%r30)
	std %r3, 8(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	or %r5, %r30, %r30
	addi %r6, %r31, 0
	li %r7, 1
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	li %r0, 0
	std %r0, 272(%r31)
	std %r0, 280(%r31)
	addi %r3, %r31, 0
	addi %r4, %r31, 272
	or %r5, %r19, %r19
214:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 214b
	ld %r3, 272(%r31)
	ld %r4, 256(%r31)
	xor %r3, %r3, %r4
	ld %r4, 280(%r31)
	ld %r5, 264(%r31)
	xor %r4, %r4, %r5
	or %r3, %r3, %r4
	li %r4, 0
	subf %r4, %r3, %r4
	or %r3, %r3, %r4
	rldicl %r3, %r3, 1, 63
	li %r4, 1
	subf %r3, %r3, %r4
	b 27f
26:
	li %r3, 0
27:
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 2592
	blr

vg_aes_gcm_seal:
	stdu %r1, -2672(%r1)
	addi %r12, %r1, 0
	ld %r0, 2768(%r12)
	std %r0, 96(%r12)
	addi %r0, %r12, 112
	std %r0, 104(%r12)
	addi %r12, %r1, 0
	ld %r12, 104(%r12)
	std %r18, 128(%r12)
	std %r19, 136(%r12)
	std %r20, 144(%r12)
	std %r21, 152(%r12)
	std %r22, 160(%r12)
	std %r23, 168(%r12)
	std %r24, 176(%r12)
	std %r25, 184(%r12)
	std %r26, 192(%r12)
	std %r27, 200(%r12)
	std %r28, 208(%r12)
	std %r29, 216(%r12)
	std %r30, 224(%r12)
	std %r31, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	or %r31, %r12, %r12
	or %r29, %r3, %r3
	or %r28, %r4, %r4
	addi %r30, %r31, 16
	or %r24, %r5, %r5
	or %r25, %r6, %r6
	or %r18, %r6, %r6
	or %r21, %r7, %r7
	or %r22, %r8, %r8
	or %r27, %r9, %r9
	or %r23, %r10, %r10
	addi %r12, %r1, 0
	ld %r20, 96(%r12)
	addi %r6, %r25, -12
	cmpldi %cr0, %r6, 0
	beq %cr0, 20f
	li %r0, 0
	std %r0, 0(%r30)
	std %r0, 8(%r30)
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 22f
	cmpldi %cr0, %r26, 0
	beq %cr0, 24f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 26f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 28f
	b 29f
28:
	or %r5, %r25, %r25
29:
	b 27f
26:
27:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
210:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 211f
	b 212f
211:
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
212:
	b 25f
24:
25:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 213f
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 214f
213:
214:
	cmpldi %cr0, %r25, 0
	beq %cr0, 215f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
217:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 217b
	b 216f
215:
216:
	b 23f
22:
23:
	li %r0, 15
	and %r26, %r18, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 218f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
220:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 219f
218:
219:
	li %r24, 0
	or %r26, %r18, %r18
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 21f
20:
	lwz %r3, 0(%r24)
	lwz %r4, 4(%r24)
	lwz %r5, 8(%r24)
	lis %r6, 256
	stw %r3, 0(%r30)
	stw %r4, 4(%r30)
	stw %r5, 8(%r30)
	stw %r6, 12(%r30)
21:
	lwz %r3, 0(%r30)
	lwz %r4, 4(%r30)
	lwz %r5, 8(%r30)
	addi %r7, %r30, 12
	li %r8, 0
	lwbrx %r6, %r7, %r8
	addi %r6, %r6, 1
	stw %r3, 48(%r30)
	stw %r4, 52(%r30)
	stw %r5, 56(%r30)
	addi %r7, %r30, 60
	stwbrx %r6, %r7, %r8
	std %r8, 16(%r30)
	std %r8, 24(%r30)
	or %r24, %r21, %r21
	or %r25, %r22, %r22
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 221f
	cmpldi %cr0, %r26, 0
	beq %cr0, 223f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 225f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 227f
	b 228f
227:
	or %r5, %r25, %r25
228:
	b 226f
225:
226:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
229:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 229b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 230f
	b 231f
230:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
231:
	b 224f
223:
224:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 232f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 233f
232:
233:
	cmpldi %cr0, %r25, 0
	beq %cr0, 234f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
236:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 236b
	b 235f
234:
235:
	b 222f
221:
222:
	li %r0, 15
	and %r26, %r22, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 237f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
239:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 239b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 238f
237:
238:
	rldicl %r12, %r23, 55, 9
	cmpldi %cr0, %r12, 0
	beq %cr0, 240f
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r6, %r30, 16
	or %r7, %r27, %r27
	rldicl %r8, %r23, 60, 4
	addi %r9, %r31, 448
	bl {vg_aes_gcm_encrypt_blocks}
	li %r0, 15
	and %r25, %r23, %r0
	subf %r12, %r25, %r23
	add %r24, %r27, %r12
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 242f
	li %r0, 0
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	addi %r6, %r30, 64
	li %r7, 1
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	addi %r3, %r30, 64
	or %r4, %r24, %r24
	or %r5, %r25, %r25
244:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 244b
	b 243f
242:
243:
	cmpldi %cr0, %r25, 0
	beq %cr0, 245f
	cmpldi %cr0, %r26, 0
	beq %cr0, 247f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 249f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 251f
	b 252f
251:
	or %r5, %r25, %r25
252:
	b 250f
249:
250:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
253:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 253b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 254f
	b 255f
254:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
255:
	b 248f
247:
248:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 256f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 257f
256:
257:
	cmpldi %cr0, %r25, 0
	beq %cr0, 258f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
260:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 260b
	b 259f
258:
259:
	b 246f
245:
246:
	cmpldi %cr0, %r23, 0
	beq %cr0, 261f
	li %r0, 15
	and %r26, %r23, %r0
	b 262f
261:
	li %r0, 15
	and %r26, %r22, %r0
262:
	cmpldi %cr0, %r26, 0
	beq %cr0, 263f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
265:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 265b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 264f
263:
264:
	or %r24, %r22, %r22
	or %r26, %r23, %r23
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	ld %r3, 16(%r30)
	std %r3, 0(%r31)
	ld %r3, 24(%r30)
	std %r3, 8(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	or %r5, %r30, %r30
	addi %r6, %r31, 0
	li %r7, 1
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	b 241f
240:
	or %r24, %r27, %r27
	or %r25, %r23, %r23
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 266f
	cmpldi %cr0, %r26, 0
	beq %cr0, 268f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 270f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 272f
	b 273f
272:
	or %r5, %r25, %r25
273:
	b 271f
270:
271:
	addi %r3, %r30, 64
	add %r3, %r3, %r26
	or %r4, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
274:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 274b
	b 269f
268:
269:
	or %r6, %r24, %r24
	rldicl %r7, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r7, 0
	beq %cr0, 275f
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	b 276f
275:
276:
	cmpldi %cr0, %r25, 0
	beq %cr0, 277f
	li %r0, 0
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	addi %r6, %r30, 64
	li %r7, 1
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	addi %r3, %r30, 64
	or %r4, %r24, %r24
	or %r5, %r25, %r25
279:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 279b
	b 278f
277:
278:
	b 267f
266:
267:
	or %r24, %r27, %r27
	or %r25, %r23, %r23
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 280f
	cmpldi %cr0, %r26, 0
	beq %cr0, 282f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 284f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 286f
	b 287f
286:
	or %r5, %r25, %r25
287:
	b 285f
284:
285:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
288:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 288b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 289f
	b 290f
289:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
290:
	b 283f
282:
283:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 291f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 292f
291:
292:
	cmpldi %cr0, %r25, 0
	beq %cr0, 293f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
295:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 295b
	b 294f
293:
294:
	b 281f
280:
281:
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 296f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
298:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 298b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 297f
296:
297:
	or %r24, %r22, %r22
	or %r26, %r23, %r23
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	ld %r3, 16(%r30)
	std %r3, 0(%r31)
	ld %r3, 24(%r30)
	std %r3, 8(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	or %r5, %r30, %r30
	addi %r6, %r31, 0
	li %r7, 1
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
241:
	ld %r3, 0(%r31)
	std %r3, 0(%r20)
	ld %r3, 8(%r31)
	std %r3, 8(%r20)
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 2672
	blr

vg_aes_gcm_open:
	stdu %r1, -2688(%r1)
	addi %r12, %r1, 0
	ld %r0, 2784(%r12)
	std %r0, 96(%r12)
	ld %r0, 2792(%r12)
	std %r0, 104(%r12)
	addi %r0, %r12, 120
	std %r0, 112(%r12)
	addi %r12, %r1, 0
	ld %r12, 112(%r12)
	std %r18, 128(%r12)
	std %r19, 136(%r12)
	std %r20, 144(%r12)
	std %r21, 152(%r12)
	std %r22, 160(%r12)
	std %r23, 168(%r12)
	std %r24, 176(%r12)
	std %r25, 184(%r12)
	std %r26, 192(%r12)
	std %r27, 200(%r12)
	std %r28, 208(%r12)
	std %r29, 216(%r12)
	std %r30, 224(%r12)
	std %r31, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	or %r31, %r12, %r12
	or %r29, %r3, %r3
	or %r28, %r4, %r4
	addi %r30, %r31, 16
	or %r24, %r5, %r5
	or %r25, %r6, %r6
	or %r18, %r6, %r6
	or %r21, %r7, %r7
	or %r22, %r8, %r8
	or %r27, %r9, %r9
	or %r23, %r10, %r10
	addi %r12, %r1, 0
	ld %r20, 96(%r12)
	ld %r19, 104(%r12)
	li %r25, 0
	rldicl %r0, %r19, 62, 2
	cmpldi %cr0, %r0, 0
	beq %cr0, 20f
	rldicl %r0, %r19, 60, 4
	cmpldi %cr0, %r0, 0
	beq %cr0, 22f
	addi %r0, %r19, -16
	cmpldi %cr0, %r0, 0
	beq %cr0, 24f
	b 25f
24:
	li %r25, 1
25:
	b 23f
22:
	li %r25, 1
23:
	b 21f
20:
21:
	cmpldi %cr0, %r25, 0
	beq %cr0, 26f
	or %r25, %r18, %r18
	addi %r6, %r25, -12
	cmpldi %cr0, %r6, 0
	beq %cr0, 28f
	li %r0, 0
	std %r0, 0(%r30)
	std %r0, 8(%r30)
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 210f
	cmpldi %cr0, %r26, 0
	beq %cr0, 212f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 214f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 216f
	b 217f
216:
	or %r5, %r25, %r25
217:
	b 215f
214:
215:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
218:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 218b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 219f
	b 220f
219:
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
220:
	b 213f
212:
213:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 221f
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 222f
221:
222:
	cmpldi %cr0, %r25, 0
	beq %cr0, 223f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
225:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 225b
	b 224f
223:
224:
	b 211f
210:
211:
	li %r0, 15
	and %r26, %r18, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 226f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
228:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 228b
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 227f
226:
227:
	li %r24, 0
	or %r26, %r18, %r18
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 0
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 29f
28:
	lwz %r3, 0(%r24)
	lwz %r4, 4(%r24)
	lwz %r5, 8(%r24)
	lis %r6, 256
	stw %r3, 0(%r30)
	stw %r4, 4(%r30)
	stw %r5, 8(%r30)
	stw %r6, 12(%r30)
29:
	lwz %r3, 0(%r30)
	lwz %r4, 4(%r30)
	lwz %r5, 8(%r30)
	addi %r7, %r30, 12
	li %r8, 0
	lwbrx %r6, %r7, %r8
	addi %r6, %r6, 1
	stw %r3, 48(%r30)
	stw %r4, 52(%r30)
	stw %r5, 56(%r30)
	addi %r7, %r30, 60
	stwbrx %r6, %r7, %r8
	std %r8, 16(%r30)
	std %r8, 24(%r30)
	or %r24, %r21, %r21
	or %r25, %r22, %r22
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 229f
	cmpldi %cr0, %r26, 0
	beq %cr0, 231f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 233f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 235f
	b 236f
235:
	or %r5, %r25, %r25
236:
	b 234f
233:
234:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
237:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 237b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 238f
	b 239f
238:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
239:
	b 232f
231:
232:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 240f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 241f
240:
241:
	cmpldi %cr0, %r25, 0
	beq %cr0, 242f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
244:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 244b
	b 243f
242:
243:
	b 230f
229:
230:
	li %r0, 15
	and %r26, %r22, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 245f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
247:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 247b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 246f
245:
246:
	or %r24, %r27, %r27
	or %r25, %r23, %r23
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 248f
	cmpldi %cr0, %r26, 0
	beq %cr0, 250f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 252f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 254f
	b 255f
254:
	or %r5, %r25, %r25
255:
	b 253f
252:
253:
	addi %r4, %r30, 32
	add %r4, %r4, %r26
	or %r3, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
	add %r26, %r26, %r5
256:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 256b
	addi %r6, %r26, -16
	cmpldi %cr0, %r6, 0
	beq %cr0, 257f
	b 258f
257:
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r30, 32
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
258:
	b 251f
250:
251:
	or %r5, %r24, %r24
	rldicl %r6, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r6, 0
	beq %cr0, 259f
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 260f
259:
260:
	cmpldi %cr0, %r25, 0
	beq %cr0, 261f
	or %r3, %r24, %r24
	addi %r4, %r30, 32
	or %r5, %r25, %r25
263:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 263b
	b 262f
261:
262:
	b 249f
248:
249:
	li %r0, 15
	and %r26, %r23, %r0
	cmpldi %cr0, %r26, 0
	beq %cr0, 264f
	li %r0, 0
	std %r0, 96(%r31)
	std %r0, 104(%r31)
	addi %r3, %r30, 32
	addi %r4, %r31, 96
	or %r5, %r26, %r26
266:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 266b
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	b 265f
264:
265:
	or %r24, %r22, %r22
	or %r26, %r23, %r23
	rldicr %r3, %r24, 3, 60
	rldicr %r4, %r26, 3, 60
	addi %r5, %r31, 96
	li %r6, 0
	stdbrx %r3, %r5, %r6
	li %r6, 8
	stdbrx %r4, %r5, %r6
	addi %r3, %r29, 240
	addi %r4, %r30, 16
	addi %r5, %r31, 96
	li %r6, 1
	addi %r7, %r31, 512
	bl {vg_ghash}
	ld %r3, 16(%r30)
	std %r3, 112(%r31)
	ld %r3, 24(%r30)
	std %r3, 120(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	or %r5, %r30, %r30
	addi %r6, %r31, 112
	li %r7, 1
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	li %r0, 0
	std %r0, 256(%r31)
	std %r0, 264(%r31)
	or %r3, %r20, %r20
	addi %r4, %r31, 256
	or %r5, %r19, %r19
267:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 267b
	li %r0, 0
	std %r0, 272(%r31)
	std %r0, 280(%r31)
	addi %r3, %r31, 112
	addi %r4, %r31, 272
	or %r5, %r19, %r19
268:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 268b
	ld %r3, 272(%r31)
	ld %r4, 256(%r31)
	xor %r3, %r3, %r4
	ld %r4, 280(%r31)
	ld %r5, 264(%r31)
	xor %r4, %r4, %r5
	or %r3, %r3, %r4
	li %r4, 0
	subf %r4, %r3, %r4
	or %r3, %r3, %r4
	rldicl %r3, %r3, 1, 63
	li %r4, 1
	subf %r3, %r3, %r4
	or %r19, %r3, %r3
	cmpldi %cr0, %r19, 0
	beq %cr0, 269f
	or %r24, %r27, %r27
	or %r25, %r23, %r23
	li %r26, 0
	cmpldi %cr0, %r25, 0
	beq %cr0, 271f
	cmpldi %cr0, %r26, 0
	beq %cr0, 273f
	li %r5, 16
	subf %r5, %r26, %r5
	rldicl %r6, %r25, 60, 4
	cmpldi %cr0, %r6, 0
	bne %cr0, 275f
	subf %r6, %r5, %r25
	rldicl %r6, %r6, 1, 63
	cmpldi %cr0, %r6, 0
	bne %cr0, 277f
	b 278f
277:
	or %r5, %r25, %r25
278:
	b 276f
275:
276:
	addi %r3, %r30, 64
	add %r3, %r3, %r26
	or %r4, %r24, %r24
	add %r24, %r24, %r5
	subf %r25, %r5, %r25
279:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 279b
	b 274f
273:
274:
	or %r6, %r24, %r24
	rldicl %r7, %r25, 60, 4
	li %r0, 15
	and %r8, %r25, %r0
	subf %r9, %r8, %r25
	add %r24, %r24, %r9
	or %r25, %r8, %r8
	cmpldi %cr0, %r7, 0
	beq %cr0, 280f
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	b 281f
280:
281:
	cmpldi %cr0, %r25, 0
	beq %cr0, 282f
	li %r0, 0
	std %r0, 64(%r30)
	std %r0, 72(%r30)
	addi %r6, %r30, 64
	li %r7, 1
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r5, %r30, 48
	addi %r8, %r31, 512
	bl {vg_aes_ctr32}
	addi %r3, %r30, 64
	or %r4, %r24, %r24
	or %r5, %r25, %r25
284:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 284b
	b 283f
282:
283:
	b 272f
271:
272:
	b 270f
269:
270:
	or %r3, %r19, %r19
	b 27f
26:
	li %r3, 0
27:
	or %r12, %r31, %r31
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r18, 128(%r12)
	ld %r19, 136(%r12)
	ld %r20, 144(%r12)
	ld %r21, 152(%r12)
	ld %r22, 160(%r12)
	ld %r23, 168(%r12)
	ld %r24, 176(%r12)
	ld %r25, 184(%r12)
	ld %r26, 192(%r12)
	ld %r27, 200(%r12)
	ld %r28, 208(%r12)
	ld %r29, 216(%r12)
	ld %r30, 224(%r12)
	ld %r31, 232(%r12)
	addi %r1, %r1, 2688
	blr

vg_aes_gcm_seal_gather:
	stdu %r1, -160(%r1)
	addi %r12, %r1, 0
	std %r3, 104(%r12)
	std %r4, 112(%r12)
	std %r5, 120(%r12)
	std %r6, 128(%r12)
	std %r7, 136(%r12)
	std %r8, 144(%r12)
	mflr %r0
	std %r0, 152(%r12)
	ld %r0, 272(%r12)
	std %r0, 96(%r12)
	or %r7, %r9, %r9
	or %r8, %r10, %r10
	ld %r9, 256(%r12)
	ld %r0, 264(%r12)
	rldicl %r0, %r0, 55, 9
	cmpldi %cr0, %r0, 0
	beq %cr0, 20f
	ld %r3, 8(%r7)
	add %r9, %r9, %r3
	addi %r7, %r7, 16
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	beq %cr0, 22f
24:
	ld %r3, 0(%r7)
	ld %r4, 8(%r7)
	addi %r7, %r7, 16
	rldicl %r5, %r4, 61, 3
	cmpldi %cr0, %r5, 0
	beq %cr0, 25f
27:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 27b
	b 26f
25:
26:
	li %r6, 7
	and %r4, %r4, %r6
	cmpldi %cr0, %r4, 0
	beq %cr0, 28f
210:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 210b
	b 29f
28:
29:
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 24b
	b 23f
22:
23:
	rldicr %r11, %r10, 4, 59
	subf %r11, %r11, %r7
	ld %r9, 0(%r11)
	ld %r10, 8(%r11)
	ld %r3, 104(%r12)
	ld %r4, 112(%r12)
	ld %r5, 120(%r12)
	ld %r6, 128(%r12)
	ld %r7, 136(%r12)
	ld %r8, 144(%r12)
	ld %r0, 256(%r12)
	std %r0, 96(%r12)
	ld %r0, 264(%r12)
	std %r0, 104(%r12)
	ld %r0, 272(%r12)
	std %r0, 112(%r12)
	bl {vg_aes_gcm_seal_split}
	addi %r12, %r1, 0
	ld %r0, 152(%r12)
	mtlr %r0
	b 21f
20:
	cmpldi %cr0, %r8, 0
	beq %cr0, 211f
213:
	ld %r3, 0(%r7)
	ld %r4, 8(%r7)
	addi %r7, %r7, 16
	rldicl %r5, %r4, 61, 3
	cmpldi %cr0, %r5, 0
	beq %cr0, 214f
216:
	ld %r0, 0(%r3)
	std %r0, 0(%r9)
	addi %r3, %r3, 8
	addi %r9, %r9, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 216b
	b 215f
214:
215:
	li %r6, 7
	and %r4, %r4, %r6
	cmpldi %cr0, %r4, 0
	beq %cr0, 217f
219:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 219b
	b 218f
217:
218:
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 213b
	b 212f
211:
212:
	ld %r3, 104(%r12)
	ld %r4, 112(%r12)
	ld %r5, 120(%r12)
	ld %r6, 128(%r12)
	ld %r7, 136(%r12)
	ld %r8, 144(%r12)
	ld %r9, 256(%r12)
	ld %r10, 264(%r12)
	bl {vg_aes_gcm_seal}
	addi %r12, %r1, 0
	ld %r0, 152(%r12)
	mtlr %r0
21:
	addi %r1, %r1, 160
	blr
