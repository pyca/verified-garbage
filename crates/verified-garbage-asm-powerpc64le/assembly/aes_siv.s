// The functions of `src/aes_siv.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_siv_init:
	stdu %r1, -2592(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 2208(%r6)
	std %r14, 2176(%r6)
	std %r15, 2184(%r6)
	std %r16, 2192(%r6)
	std %r17, 2200(%r6)
	or %r14, %r3, %r3
	rldicl %r15, %r4, 63, 1
	or %r16, %r5, %r5
	or %r17, %r6, %r6
	or %r4, %r15, %r15
	bl {vg_aes_expand_key_scratch}
	or %r3, %r16, %r16
	rldicl %r4, %r15, 62, 2
	addi %r4, %r4, 6
	addi %r5, %r16, 240
	or %r6, %r17, %r17
	bl {vg_cmac_aes_subkeys}
	add %r3, %r14, %r15
	or %r4, %r15, %r15
	addi %r5, %r16, 272
	or %r6, %r17, %r17
	bl {vg_aes_expand_key_scratch}
	ld %r0, 2208(%r17)
	ld %r14, 2176(%r17)
	ld %r15, 2184(%r17)
	ld %r16, 2192(%r17)
	ld %r17, 2200(%r17)
	mtlr %r0
	addi %r1, %r1, 2592
	blr

vg_aes_siv_encrypt:
	stdu %r1, -2608(%r1)
	addi %r10, %r1, 32
	mflr %r0
	std %r15, 136(%r10)
	std %r16, 144(%r10)
	std %r17, 152(%r10)
	std %r18, 160(%r10)
	std %r19, 168(%r10)
	std %r20, 176(%r10)
	std %r21, 184(%r10)
	std %r22, 192(%r10)
	std %r23, 200(%r10)
	std %r24, 208(%r10)
	std %r25, 216(%r10)
	std %r14, 128(%r10)
	std %r0, 224(%r10)
	or %r14, %r10, %r10
	or %r15, %r3, %r3
	or %r16, %r4, %r4
	or %r17, %r5, %r5
	or %r18, %r6, %r6
	or %r22, %r7, %r7
	or %r23, %r8, %r8
	or %r24, %r9, %r9
	li %r0, 0
	std %r0, 16(%r14)
	std %r0, 24(%r14)
	li %r0, 0
	std %r0, 272(%r14)
	std %r0, 280(%r14)
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 272
	addi %r8, %r14, 384
	addi %r6, %r14, 16
	li %r7, 16
	bl {vg_cmac_aes_finalize}
	cmpldi %cr0, %r18, 0
	beq %cr0, 20f
22:
	ld %r19, 0(%r17)
	ld %r20, 8(%r17)
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	li %r21, 0
	cmpldi %cr0, %r20, 0
	beq %cr0, 23f
	addi %r21, %r20, -1
	rldicl %r21, %r21, 60, 4
	rldicr %r21, %r21, 4, 59
	b 24f
23:
24:
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 240
	addi %r8, %r14, 384
	or %r6, %r19, %r19
	rldicl %r7, %r21, 60, 4
	bl {vg_cmac_aes_update}
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 240
	addi %r8, %r14, 384
	add %r6, %r19, %r21
	subf %r7, %r21, %r20
	bl {vg_cmac_aes_finalize}
	li %r11, 272
	ldbrx %r9, %r14, %r11
	li %r11, 280
	ldbrx %r10, %r14, %r11
	rldicl %r11, %r9, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r10, 1, 63
	rldicr %r9, %r9, 1, 62
	or %r9, %r9, %r12
	rldicr %r10, %r10, 1, 62
	xor %r10, %r10, %r11
	li %r11, 272
	stdbrx %r9, %r14, %r11
	li %r11, 280
	stdbrx %r10, %r14, %r11
	ld %r9, 272(%r14)
	ld %r10, 240(%r14)
	xor %r9, %r9, %r10
	std %r9, 272(%r14)
	ld %r9, 280(%r14)
	ld %r10, 248(%r14)
	xor %r9, %r9, %r10
	std %r9, 280(%r14)
	addi %r17, %r17, 16
	addi %r18, %r18, -1
	cmpldi %cr0, %r18, 0
	bne %cr0, 22b
	b 21f
20:
21:
	or %r19, %r22, %r22
	or %r20, %r23, %r23
	rldicl %r9, %r20, 60, 4
	cmpldi %cr0, %r9, 0
	beq %cr0, 25f
	addi %r9, %r20, -1
	rldicl %r9, %r9, 60, 4
	li %r21, 0
	cmpldi %cr0, %r9, 0
	beq %cr0, 27f
	addi %r9, %r9, -1
	rldicr %r21, %r9, 4, 59
	b 28f
27:
28:
	add %r3, %r19, %r21
	addi %r9, %r14, 32
	subf %r4, %r21, %r20
29:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 29b
	subf %r11, %r21, %r20
	add %r11, %r14, %r11
	ld %r9, 16(%r11)
	ld %r10, 272(%r14)
	xor %r9, %r9, %r10
	std %r9, 16(%r11)
	ld %r9, 24(%r11)
	ld %r10, 280(%r14)
	xor %r9, %r9, %r10
	std %r9, 24(%r11)
	li %r0, 0
	std %r0, 0(%r14)
	std %r0, 8(%r14)
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 0
	addi %r8, %r14, 384
	or %r6, %r19, %r19
	rldicl %r7, %r21, 60, 4
	bl {vg_cmac_aes_update}
	addi %r9, %r20, -1
	rldicl %r9, %r9, 60, 4
	li %r25, 0
	cmpldi %cr0, %r9, 0
	beq %cr0, 210f
	li %r25, 1
	b 211f
210:
211:
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 0
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	or %r7, %r25, %r25
	bl {vg_cmac_aes_update}
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 0
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	rldicr %r9, %r25, 4, 59
	add %r6, %r6, %r9
	subf %r7, %r21, %r20
	subf %r7, %r9, %r7
	bl {vg_cmac_aes_finalize}
	b 26f
25:
	li %r0, 0
	std %r0, 32(%r14)
	std %r0, 40(%r14)
	cmpldi %cr0, %r20, 0
	beq %cr0, 212f
	or %r3, %r19, %r19
	addi %r9, %r14, 32
	or %r4, %r20, %r20
214:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 214b
	b 213f
212:
213:
	add %r9, %r14, %r20
	li %r0, 128
	stb %r0, 32(%r9)
	li %r11, 272
	ldbrx %r9, %r14, %r11
	li %r11, 280
	ldbrx %r10, %r14, %r11
	rldicl %r11, %r9, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r10, 1, 63
	rldicr %r9, %r9, 1, 62
	or %r9, %r9, %r12
	rldicr %r10, %r10, 1, 62
	xor %r10, %r10, %r11
	li %r11, 256
	stdbrx %r9, %r14, %r11
	li %r11, 264
	stdbrx %r10, %r14, %r11
	ld %r9, 32(%r14)
	ld %r10, 256(%r14)
	xor %r9, %r9, %r10
	std %r9, 32(%r14)
	ld %r9, 40(%r14)
	ld %r10, 264(%r14)
	xor %r9, %r9, %r10
	std %r9, 40(%r14)
	li %r0, 0
	std %r0, 0(%r14)
	std %r0, 8(%r14)
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 0
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	li %r7, 16
	bl {vg_cmac_aes_finalize}
26:
	ld %r9, 0(%r14)
	std %r9, 64(%r14)
	ld %r9, 8(%r14)
	li %r10, 128
	rldicr %r11, %r10, 32, 31
	or %r10, %r10, %r11
	or %r9, %r9, %r10
	xor %r9, %r9, %r10
	std %r9, 72(%r14)
	or %r19, %r22, %r22
	or %r20, %r23, %r23
	ld %r9, 64(%r14)
	std %r9, 96(%r14)
	ld %r9, 72(%r14)
	std %r9, 104(%r14)
	rldicl %r7, %r20, 60, 4
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	addi %r3, %r15, 272
	or %r4, %r16, %r16
	addi %r5, %r14, 96
	addi %r8, %r14, 384
	or %r6, %r19, %r19
	bl {vg_aes_ctr32}
	rldicl %r9, %r20, 60, 4
	rldicr %r9, %r9, 33, 30
	rldicl %r9, %r9, 31, 33
	li %r11, 72
	ldbrx %r10, %r14, %r11
	add %r10, %r10, %r9
	stdbrx %r10, %r14, %r11
	rldicr %r9, %r9, 4, 59
	add %r19, %r19, %r9
	subf %r20, %r9, %r20
	cmpldi %cr0, %r20, 0
	beq %cr0, 215f
217:
	li %r0, 0
	std %r0, 80(%r14)
	std %r0, 88(%r14)
	ld %r9, 64(%r14)
	std %r9, 96(%r14)
	ld %r9, 72(%r14)
	std %r9, 104(%r14)
	addi %r3, %r15, 272
	or %r4, %r16, %r16
	addi %r5, %r14, 96
	addi %r8, %r14, 384
	addi %r6, %r14, 80
	li %r7, 1
	bl {vg_aes_ctr32}
	rldicl %r10, %r20, 60, 4
	or %r4, %r20, %r20
	addi %r3, %r14, 80
	or %r9, %r19, %r19
	cmpldi %cr0, %r10, 0
	beq %cr0, 218f
	li %r4, 16
	b 219f
218:
219:
220:
	lbz %r0, 0(%r3)
	lbz %r5, 0(%r9)
	xor %r0, %r0, %r5
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 220b
	li %r11, 72
	ldbrx %r10, %r14, %r11
	addi %r10, %r10, 1
	stdbrx %r10, %r14, %r11
	addi %r19, %r19, 16
	rldicl %r9, %r20, 60, 4
	cmpldi %cr0, %r9, 0
	beq %cr0, 221f
	addi %r20, %r20, -16
	b 222f
221:
	li %r20, 0
222:
	cmpldi %cr0, %r20, 0
	bne %cr0, 217b
	b 216f
215:
216:
	ld %r9, 0(%r14)
	std %r9, 0(%r24)
	ld %r9, 8(%r14)
	std %r9, 8(%r24)
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
	addi %r1, %r1, 2608
	blr

vg_aes_siv_decrypt:
	stdu %r1, -2608(%r1)
	addi %r10, %r1, 32
	mflr %r0
	std %r15, 136(%r10)
	std %r16, 144(%r10)
	std %r17, 152(%r10)
	std %r18, 160(%r10)
	std %r19, 168(%r10)
	std %r20, 176(%r10)
	std %r21, 184(%r10)
	std %r22, 192(%r10)
	std %r23, 200(%r10)
	std %r24, 208(%r10)
	std %r25, 216(%r10)
	std %r14, 128(%r10)
	std %r0, 224(%r10)
	or %r14, %r10, %r10
	or %r15, %r3, %r3
	or %r16, %r4, %r4
	or %r17, %r5, %r5
	or %r18, %r6, %r6
	or %r22, %r7, %r7
	or %r23, %r8, %r8
	or %r24, %r9, %r9
	li %r0, 0
	std %r0, 16(%r14)
	std %r0, 24(%r14)
	li %r0, 0
	std %r0, 272(%r14)
	std %r0, 280(%r14)
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 272
	addi %r8, %r14, 384
	addi %r6, %r14, 16
	li %r7, 16
	bl {vg_cmac_aes_finalize}
	cmpldi %cr0, %r18, 0
	beq %cr0, 20f
22:
	ld %r19, 0(%r17)
	ld %r20, 8(%r17)
	li %r0, 0
	std %r0, 240(%r14)
	std %r0, 248(%r14)
	li %r21, 0
	cmpldi %cr0, %r20, 0
	beq %cr0, 23f
	addi %r21, %r20, -1
	rldicl %r21, %r21, 60, 4
	rldicr %r21, %r21, 4, 59
	b 24f
23:
24:
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 240
	addi %r8, %r14, 384
	or %r6, %r19, %r19
	rldicl %r7, %r21, 60, 4
	bl {vg_cmac_aes_update}
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 240
	addi %r8, %r14, 384
	add %r6, %r19, %r21
	subf %r7, %r21, %r20
	bl {vg_cmac_aes_finalize}
	li %r11, 272
	ldbrx %r9, %r14, %r11
	li %r11, 280
	ldbrx %r10, %r14, %r11
	rldicl %r11, %r9, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r10, 1, 63
	rldicr %r9, %r9, 1, 62
	or %r9, %r9, %r12
	rldicr %r10, %r10, 1, 62
	xor %r10, %r10, %r11
	li %r11, 272
	stdbrx %r9, %r14, %r11
	li %r11, 280
	stdbrx %r10, %r14, %r11
	ld %r9, 272(%r14)
	ld %r10, 240(%r14)
	xor %r9, %r9, %r10
	std %r9, 272(%r14)
	ld %r9, 280(%r14)
	ld %r10, 248(%r14)
	xor %r9, %r9, %r10
	std %r9, 280(%r14)
	addi %r17, %r17, 16
	addi %r18, %r18, -1
	cmpldi %cr0, %r18, 0
	bne %cr0, 22b
	b 21f
20:
21:
	or %r19, %r22, %r22
	or %r20, %r23, %r23
	ld %r9, 0(%r24)
	std %r9, 0(%r14)
	ld %r9, 8(%r24)
	std %r9, 8(%r14)
	ld %r9, 0(%r14)
	std %r9, 64(%r14)
	ld %r9, 8(%r14)
	li %r10, 128
	rldicr %r11, %r10, 32, 31
	or %r10, %r10, %r11
	or %r9, %r9, %r10
	xor %r9, %r9, %r10
	std %r9, 72(%r14)
	or %r19, %r22, %r22
	or %r20, %r23, %r23
	ld %r9, 64(%r14)
	std %r9, 96(%r14)
	ld %r9, 72(%r14)
	std %r9, 104(%r14)
	rldicl %r7, %r20, 60, 4
	rldicr %r7, %r7, 33, 30
	rldicl %r7, %r7, 31, 33
	addi %r3, %r15, 272
	or %r4, %r16, %r16
	addi %r5, %r14, 96
	addi %r8, %r14, 384
	or %r6, %r19, %r19
	bl {vg_aes_ctr32}
	rldicl %r9, %r20, 60, 4
	rldicr %r9, %r9, 33, 30
	rldicl %r9, %r9, 31, 33
	li %r11, 72
	ldbrx %r10, %r14, %r11
	add %r10, %r10, %r9
	stdbrx %r10, %r14, %r11
	rldicr %r9, %r9, 4, 59
	add %r19, %r19, %r9
	subf %r20, %r9, %r20
	cmpldi %cr0, %r20, 0
	beq %cr0, 25f
27:
	li %r0, 0
	std %r0, 80(%r14)
	std %r0, 88(%r14)
	ld %r9, 64(%r14)
	std %r9, 96(%r14)
	ld %r9, 72(%r14)
	std %r9, 104(%r14)
	addi %r3, %r15, 272
	or %r4, %r16, %r16
	addi %r5, %r14, 96
	addi %r8, %r14, 384
	addi %r6, %r14, 80
	li %r7, 1
	bl {vg_aes_ctr32}
	rldicl %r10, %r20, 60, 4
	or %r4, %r20, %r20
	addi %r3, %r14, 80
	or %r9, %r19, %r19
	cmpldi %cr0, %r10, 0
	beq %cr0, 28f
	li %r4, 16
	b 29f
28:
29:
210:
	lbz %r0, 0(%r3)
	lbz %r5, 0(%r9)
	xor %r0, %r0, %r5
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 210b
	li %r11, 72
	ldbrx %r10, %r14, %r11
	addi %r10, %r10, 1
	stdbrx %r10, %r14, %r11
	addi %r19, %r19, 16
	rldicl %r9, %r20, 60, 4
	cmpldi %cr0, %r9, 0
	beq %cr0, 211f
	addi %r20, %r20, -16
	b 212f
211:
	li %r20, 0
212:
	cmpldi %cr0, %r20, 0
	bne %cr0, 27b
	b 26f
25:
26:
	or %r19, %r22, %r22
	or %r20, %r23, %r23
	rldicl %r9, %r20, 60, 4
	cmpldi %cr0, %r9, 0
	beq %cr0, 213f
	addi %r9, %r20, -1
	rldicl %r9, %r9, 60, 4
	li %r21, 0
	cmpldi %cr0, %r9, 0
	beq %cr0, 215f
	addi %r9, %r9, -1
	rldicr %r21, %r9, 4, 59
	b 216f
215:
216:
	add %r3, %r19, %r21
	addi %r9, %r14, 32
	subf %r4, %r21, %r20
217:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 217b
	subf %r11, %r21, %r20
	add %r11, %r14, %r11
	ld %r9, 16(%r11)
	ld %r10, 272(%r14)
	xor %r9, %r9, %r10
	std %r9, 16(%r11)
	ld %r9, 24(%r11)
	ld %r10, 280(%r14)
	xor %r9, %r9, %r10
	std %r9, 24(%r11)
	li %r0, 0
	std %r0, 112(%r14)
	std %r0, 120(%r14)
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 112
	addi %r8, %r14, 384
	or %r6, %r19, %r19
	rldicl %r7, %r21, 60, 4
	bl {vg_cmac_aes_update}
	addi %r9, %r20, -1
	rldicl %r9, %r9, 60, 4
	li %r25, 0
	cmpldi %cr0, %r9, 0
	beq %cr0, 218f
	li %r25, 1
	b 219f
218:
219:
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 112
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	or %r7, %r25, %r25
	bl {vg_cmac_aes_update}
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 112
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	rldicr %r9, %r25, 4, 59
	add %r6, %r6, %r9
	subf %r7, %r21, %r20
	subf %r7, %r9, %r7
	bl {vg_cmac_aes_finalize}
	b 214f
213:
	li %r0, 0
	std %r0, 32(%r14)
	std %r0, 40(%r14)
	cmpldi %cr0, %r20, 0
	beq %cr0, 220f
	or %r3, %r19, %r19
	addi %r9, %r14, 32
	or %r4, %r20, %r20
222:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 222b
	b 221f
220:
221:
	add %r9, %r14, %r20
	li %r0, 128
	stb %r0, 32(%r9)
	li %r11, 272
	ldbrx %r9, %r14, %r11
	li %r11, 280
	ldbrx %r10, %r14, %r11
	rldicl %r11, %r9, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r10, 1, 63
	rldicr %r9, %r9, 1, 62
	or %r9, %r9, %r12
	rldicr %r10, %r10, 1, 62
	xor %r10, %r10, %r11
	li %r11, 256
	stdbrx %r9, %r14, %r11
	li %r11, 264
	stdbrx %r10, %r14, %r11
	ld %r9, 32(%r14)
	ld %r10, 256(%r14)
	xor %r9, %r9, %r10
	std %r9, 32(%r14)
	ld %r9, 40(%r14)
	ld %r10, 264(%r14)
	xor %r9, %r9, %r10
	std %r9, 40(%r14)
	li %r0, 0
	std %r0, 112(%r14)
	std %r0, 120(%r14)
	or %r3, %r15, %r15
	or %r4, %r16, %r16
	addi %r5, %r14, 112
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	li %r7, 16
	bl {vg_cmac_aes_finalize}
214:
	ld %r3, 0(%r14)
	ld %r4, 112(%r14)
	xor %r3, %r3, %r4
	ld %r4, 8(%r14)
	ld %r5, 120(%r14)
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
	or %r3, %r22, %r22
	or %r4, %r23, %r23
	cmpldi %cr0, %r4, 0
	beq %cr0, 223f
225:
	lbz %r0, 0(%r3)
	and %r0, %r0, %r9
	stb %r0, 0(%r3)
	addi %r3, %r3, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 225b
	b 224f
223:
224:
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
	addi %r1, %r1, 2608
	blr
