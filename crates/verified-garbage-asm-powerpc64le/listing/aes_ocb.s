// The functions of `src/aes_ocb.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ocb_init:
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

vg_aes_ocb_seal:
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
	li %r0, 240
	ldbrx %r3, %r29, %r0
	li %r0, 248
	ldbrx %r4, %r29, %r0
	rldicl %r5, %r3, 1, 63
	li %r6, 0
	subf %r5, %r5, %r6
	li %r6, 135
	and %r5, %r5, %r6
	rldicr %r3, %r3, 1, 62
	rldicl %r6, %r4, 1, 63
	or %r3, %r3, %r6
	rldicr %r4, %r4, 1, 62
	xor %r4, %r4, %r5
	li %r0, 64
	stdbrx %r3, %r31, %r0
	li %r0, 72
	stdbrx %r4, %r31, %r0
	li %r0, 64
	ldbrx %r3, %r31, %r0
	li %r0, 72
	ldbrx %r4, %r31, %r0
	rldicl %r5, %r3, 1, 63
	li %r6, 0
	subf %r5, %r5, %r6
	li %r6, 135
	and %r5, %r5, %r6
	rldicr %r3, %r3, 1, 62
	rldicl %r6, %r4, 1, 63
	or %r3, %r3, %r6
	rldicr %r4, %r4, 1, 62
	xor %r4, %r4, %r5
	li %r0, 80
	stdbrx %r3, %r31, %r0
	li %r0, 88
	stdbrx %r4, %r31, %r0
	li %r0, 0
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	li %r0, 0
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	addi %r4, %r31, 127
	subf %r4, %r25, %r4
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	or %r3, %r24, %r24
	or %r5, %r25, %r25
20:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	li %r0, 15
	and %r3, %r19, %r0
	rldicr %r3, %r3, 4, 59
	lbz %r4, 112(%r31)
	or %r4, %r4, %r3
	stb %r4, 112(%r31)
	lbz %r4, 127(%r31)
	li %r0, 63
	and %r3, %r4, %r0
	std %r3, 288(%r31)
	li %r0, 192
	and %r4, %r4, %r0
	stb %r4, 127(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r7, %r31, 512
	addi %r5, %r31, 112
	li %r6, 1
	bl {vg_aes_encrypt_blocks}
	li %r0, 112
	ldbrx %r3, %r31, %r0
	li %r0, 120
	ldbrx %r4, %r31, %r0
	rldicr %r5, %r3, 8, 55
	rldicl %r8, %r4, 8, 56
	or %r5, %r5, %r8
	xor %r5, %r5, %r3
	ld %r6, 288(%r31)
	li %r0, 1
	and %r7, %r6, %r0
	li %r8, 0
	subf %r7, %r7, %r8
	rldicr %r8, %r3, 1, 62
	rldicl %r9, %r4, 1, 63
	or %r8, %r8, %r9
	xor %r8, %r8, %r3
	and %r8, %r8, %r7
	xor %r3, %r3, %r8
	rldicr %r8, %r4, 1, 62
	rldicl %r9, %r5, 1, 63
	or %r8, %r8, %r9
	xor %r8, %r8, %r4
	and %r8, %r8, %r7
	xor %r4, %r4, %r8
	rldicr %r8, %r5, 1, 62
	xor %r8, %r8, %r5
	and %r8, %r8, %r7
	xor %r5, %r5, %r8
	rldicl %r7, %r6, 63, 1
	li %r0, 1
	and %r7, %r7, %r0
	li %r8, 0
	subf %r7, %r7, %r8
	rldicr %r8, %r3, 2, 61
	rldicl %r9, %r4, 2, 62
	or %r8, %r8, %r9
	xor %r8, %r8, %r3
	and %r8, %r8, %r7
	xor %r3, %r3, %r8
	rldicr %r8, %r4, 2, 61
	rldicl %r9, %r5, 2, 62
	or %r8, %r8, %r9
	xor %r8, %r8, %r4
	and %r8, %r8, %r7
	xor %r4, %r4, %r8
	rldicr %r8, %r5, 2, 61
	xor %r8, %r8, %r5
	and %r8, %r8, %r7
	xor %r5, %r5, %r8
	rldicl %r7, %r6, 62, 2
	li %r0, 1
	and %r7, %r7, %r0
	li %r8, 0
	subf %r7, %r7, %r8
	rldicr %r8, %r3, 4, 59
	rldicl %r9, %r4, 4, 60
	or %r8, %r8, %r9
	xor %r8, %r8, %r3
	and %r8, %r8, %r7
	xor %r3, %r3, %r8
	rldicr %r8, %r4, 4, 59
	rldicl %r9, %r5, 4, 60
	or %r8, %r8, %r9
	xor %r8, %r8, %r4
	and %r8, %r8, %r7
	xor %r4, %r4, %r8
	rldicr %r8, %r5, 4, 59
	xor %r8, %r8, %r5
	and %r8, %r8, %r7
	xor %r5, %r5, %r8
	rldicl %r7, %r6, 61, 3
	li %r0, 1
	and %r7, %r7, %r0
	li %r8, 0
	subf %r7, %r7, %r8
	rldicr %r8, %r3, 8, 55
	rldicl %r9, %r4, 8, 56
	or %r8, %r8, %r9
	xor %r8, %r8, %r3
	and %r8, %r8, %r7
	xor %r3, %r3, %r8
	rldicr %r8, %r4, 8, 55
	rldicl %r9, %r5, 8, 56
	or %r8, %r8, %r9
	xor %r8, %r8, %r4
	and %r8, %r8, %r7
	xor %r4, %r4, %r8
	rldicr %r8, %r5, 8, 55
	xor %r8, %r8, %r5
	and %r8, %r8, %r7
	xor %r5, %r5, %r8
	rldicl %r7, %r6, 60, 4
	li %r0, 1
	and %r7, %r7, %r0
	li %r8, 0
	subf %r7, %r7, %r8
	rldicr %r8, %r3, 16, 47
	rldicl %r9, %r4, 16, 48
	or %r8, %r8, %r9
	xor %r8, %r8, %r3
	and %r8, %r8, %r7
	xor %r3, %r3, %r8
	rldicr %r8, %r4, 16, 47
	rldicl %r9, %r5, 16, 48
	or %r8, %r8, %r9
	xor %r8, %r8, %r4
	and %r8, %r8, %r7
	xor %r4, %r4, %r8
	rldicr %r8, %r5, 16, 47
	xor %r8, %r8, %r5
	and %r8, %r8, %r7
	xor %r5, %r5, %r8
	rldicl %r7, %r6, 59, 5
	li %r0, 1
	and %r7, %r7, %r0
	li %r8, 0
	subf %r7, %r7, %r8
	rldicr %r8, %r3, 32, 31
	rldicl %r9, %r4, 32, 32
	or %r8, %r8, %r9
	xor %r8, %r8, %r3
	and %r8, %r8, %r7
	xor %r3, %r3, %r8
	rldicr %r8, %r4, 32, 31
	rldicl %r9, %r5, 32, 32
	or %r8, %r8, %r9
	xor %r8, %r8, %r4
	and %r8, %r8, %r7
	xor %r4, %r4, %r8
	rldicr %r8, %r5, 32, 31
	xor %r8, %r8, %r5
	and %r8, %r8, %r7
	xor %r5, %r5, %r8
	li %r0, 16
	stdbrx %r3, %r31, %r0
	li %r0, 24
	stdbrx %r4, %r31, %r0
	li %r0, 320
	stdbrx %r3, %r31, %r0
	li %r0, 328
	stdbrx %r4, %r31, %r0
	li %r0, 0
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	li %r0, 0
	std %r0, 272(%r31)
	std %r0, 280(%r31)
	or %r24, %r21, %r21
	rldicl %r3, %r22, 60, 4
	std %r3, 304(%r31)
	li %r26, 1
	cmpldi %cr0, %r3, 0
	beq %cr0, 21f
23:
	ld %r3, 304(%r31)
	rldicl %r4, %r3, 61, 3
	cmpldi %cr0, %r4, 0
	beq %cr0, 24f
	li %r25, 8
	b 25f
24:
	or %r25, %r3, %r3
25:
	std %r25, 296(%r31)
	ld %r3, 304(%r31)
	subf %r3, %r25, %r3
	std %r3, 304(%r31)
	addi %r11, %r31, 384
26:
	ld %r3, 80(%r31)
	ld %r4, 88(%r31)
	std %r3, 96(%r31)
	std %r4, 104(%r31)
	or %r12, %r26, %r26
	li %r0, 1
	and %r5, %r12, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 27f
	b 28f
27:
29:
	li %r0, 96
	ldbrx %r3, %r31, %r0
	li %r0, 104
	ldbrx %r4, %r31, %r0
	rldicl %r5, %r3, 1, 63
	li %r6, 0
	subf %r5, %r5, %r6
	li %r6, 135
	and %r5, %r5, %r6
	rldicr %r3, %r3, 1, 62
	rldicl %r6, %r4, 1, 63
	or %r3, %r3, %r6
	rldicr %r4, %r4, 1, 62
	xor %r4, %r4, %r5
	li %r0, 96
	stdbrx %r3, %r31, %r0
	li %r0, 104
	stdbrx %r4, %r31, %r0
	rldicl %r12, %r12, 63, 1
	li %r0, 1
	and %r5, %r12, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 29b
28:
	ld %r3, 272(%r31)
	ld %r4, 96(%r31)
	xor %r3, %r3, %r4
	std %r3, 272(%r31)
	ld %r3, 280(%r31)
	ld %r4, 104(%r31)
	xor %r3, %r3, %r4
	std %r3, 280(%r31)
	ld %r3, 0(%r24)
	ld %r4, 272(%r31)
	xor %r3, %r3, %r4
	std %r3, 0(%r11)
	ld %r3, 8(%r24)
	ld %r4, 280(%r31)
	xor %r3, %r3, %r4
	std %r3, 8(%r11)
	addi %r11, %r11, 16
	addi %r24, %r24, 16
	addi %r26, %r26, 1
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 26b
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r7, %r31, 512
	addi %r5, %r31, 384
	ld %r6, 296(%r31)
	bl {vg_aes_encrypt_blocks}
	addi %r11, %r31, 384
	ld %r25, 296(%r31)
210:
	ld %r3, 48(%r31)
	ld %r4, 0(%r11)
	xor %r3, %r3, %r4
	std %r3, 48(%r31)
	ld %r3, 56(%r31)
	ld %r4, 8(%r11)
	xor %r3, %r3, %r4
	std %r3, 56(%r31)
	addi %r11, %r11, 16
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 210b
	ld %r3, 304(%r31)
	cmpldi %cr0, %r3, 0
	bne %cr0, 23b
	b 22f
21:
22:
	li %r0, 15
	and %r25, %r22, %r0
	cmpldi %cr0, %r25, 0
	beq %cr0, 211f
	ld %r3, 272(%r31)
	ld %r4, 240(%r29)
	xor %r3, %r3, %r4
	std %r3, 272(%r31)
	ld %r3, 280(%r31)
	ld %r4, 248(%r29)
	xor %r3, %r3, %r4
	std %r3, 280(%r31)
	li %r0, 0
	std %r0, 384(%r31)
	std %r0, 392(%r31)
	addi %r4, %r31, 384
	or %r3, %r24, %r24
	or %r5, %r25, %r25
213:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 213b
	li %r0, 128
	stb %r0, 0(%r4)
	ld %r3, 384(%r31)
	ld %r4, 272(%r31)
	xor %r3, %r3, %r4
	std %r3, 384(%r31)
	ld %r3, 392(%r31)
	ld %r4, 280(%r31)
	xor %r3, %r3, %r4
	std %r3, 392(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r7, %r31, 512
	addi %r5, %r31, 384
	li %r6, 1
	bl {vg_aes_encrypt_blocks}
	ld %r3, 48(%r31)
	ld %r4, 384(%r31)
	xor %r3, %r3, %r4
	std %r3, 48(%r31)
	ld %r3, 56(%r31)
	ld %r4, 392(%r31)
	xor %r3, %r3, %r4
	std %r3, 56(%r31)
	b 212f
211:
212:
	rldicl %r3, %r23, 60, 4
	cmpldi %cr0, %r3, 0
	beq %cr0, 214f
	or %r24, %r27, %r27
	rldicl %r25, %r23, 60, 4
	li %r26, 1
216:
	ld %r3, 80(%r31)
	ld %r4, 88(%r31)
	std %r3, 96(%r31)
	std %r4, 104(%r31)
	or %r12, %r26, %r26
	li %r0, 1
	and %r5, %r12, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 217f
	b 218f
217:
219:
	li %r0, 96
	ldbrx %r3, %r31, %r0
	li %r0, 104
	ldbrx %r4, %r31, %r0
	rldicl %r5, %r3, 1, 63
	li %r6, 0
	subf %r5, %r5, %r6
	li %r6, 135
	and %r5, %r5, %r6
	rldicr %r3, %r3, 1, 62
	rldicl %r6, %r4, 1, 63
	or %r3, %r3, %r6
	rldicr %r4, %r4, 1, 62
	xor %r4, %r4, %r5
	li %r0, 96
	stdbrx %r3, %r31, %r0
	li %r0, 104
	stdbrx %r4, %r31, %r0
	rldicl %r12, %r12, 63, 1
	li %r0, 1
	and %r5, %r12, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 219b
218:
	ld %r3, 16(%r31)
	ld %r4, 96(%r31)
	xor %r3, %r3, %r4
	std %r3, 16(%r31)
	ld %r3, 24(%r31)
	ld %r4, 104(%r31)
	xor %r3, %r3, %r4
	std %r3, 24(%r31)
	ld %r3, 32(%r31)
	ld %r4, 0(%r24)
	xor %r3, %r3, %r4
	std %r3, 32(%r31)
	ld %r3, 40(%r31)
	ld %r4, 8(%r24)
	xor %r3, %r3, %r4
	std %r3, 40(%r31)
	ld %r3, 0(%r24)
	ld %r4, 16(%r31)
	xor %r3, %r3, %r4
	std %r3, 0(%r24)
	ld %r3, 8(%r24)
	ld %r4, 24(%r31)
	xor %r3, %r3, %r4
	std %r3, 8(%r24)
	addi %r24, %r24, 16
	addi %r26, %r26, 1
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 216b
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r7, %r31, 512
	or %r5, %r27, %r27
	rldicl %r6, %r23, 60, 4
	bl {vg_aes_encrypt_blocks}
	ld %r3, 320(%r31)
	ld %r4, 328(%r31)
	std %r3, 16(%r31)
	std %r4, 24(%r31)
	or %r24, %r27, %r27
	rldicl %r25, %r23, 60, 4
	li %r26, 1
220:
	ld %r3, 80(%r31)
	ld %r4, 88(%r31)
	std %r3, 96(%r31)
	std %r4, 104(%r31)
	or %r12, %r26, %r26
	li %r0, 1
	and %r5, %r12, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 221f
	b 222f
221:
223:
	li %r0, 96
	ldbrx %r3, %r31, %r0
	li %r0, 104
	ldbrx %r4, %r31, %r0
	rldicl %r5, %r3, 1, 63
	li %r6, 0
	subf %r5, %r5, %r6
	li %r6, 135
	and %r5, %r5, %r6
	rldicr %r3, %r3, 1, 62
	rldicl %r6, %r4, 1, 63
	or %r3, %r3, %r6
	rldicr %r4, %r4, 1, 62
	xor %r4, %r4, %r5
	li %r0, 96
	stdbrx %r3, %r31, %r0
	li %r0, 104
	stdbrx %r4, %r31, %r0
	rldicl %r12, %r12, 63, 1
	li %r0, 1
	and %r5, %r12, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 223b
222:
	ld %r3, 16(%r31)
	ld %r4, 96(%r31)
	xor %r3, %r3, %r4
	std %r3, 16(%r31)
	ld %r3, 24(%r31)
	ld %r4, 104(%r31)
	xor %r3, %r3, %r4
	std %r3, 24(%r31)
	ld %r3, 0(%r24)
	ld %r4, 16(%r31)
	xor %r3, %r3, %r4
	std %r3, 0(%r24)
	ld %r3, 8(%r24)
	ld %r4, 24(%r31)
	xor %r3, %r3, %r4
	std %r3, 8(%r24)
	addi %r24, %r24, 16
	addi %r26, %r26, 1
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 220b
	b 215f
214:
215:
	li %r0, 15
	and %r25, %r23, %r0
	subf %r24, %r25, %r23
	add %r24, %r24, %r27
	cmpldi %cr0, %r25, 0
	beq %cr0, 224f
	ld %r3, 16(%r31)
	ld %r4, 240(%r29)
	xor %r3, %r3, %r4
	std %r3, 16(%r31)
	ld %r3, 24(%r31)
	ld %r4, 248(%r29)
	xor %r3, %r3, %r4
	std %r3, 24(%r31)
	ld %r3, 16(%r31)
	ld %r4, 24(%r31)
	std %r3, 112(%r31)
	std %r4, 120(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r7, %r31, 512
	addi %r5, %r31, 112
	li %r6, 1
	bl {vg_aes_encrypt_blocks}
	li %r0, 0
	std %r0, 256(%r31)
	std %r0, 264(%r31)
	addi %r4, %r31, 256
	or %r3, %r24, %r24
	or %r5, %r25, %r25
226:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 226b
	li %r0, 128
	stb %r0, 0(%r4)
	ld %r3, 32(%r31)
	ld %r4, 256(%r31)
	xor %r3, %r3, %r4
	std %r3, 32(%r31)
	ld %r3, 40(%r31)
	ld %r4, 264(%r31)
	xor %r3, %r3, %r4
	std %r3, 40(%r31)
	addi %r3, %r31, 112
	or %r4, %r24, %r24
	or %r5, %r25, %r25
227:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 227b
	b 225f
224:
225:
	ld %r3, 32(%r31)
	ld %r4, 40(%r31)
	std %r3, 112(%r31)
	std %r4, 120(%r31)
	ld %r3, 112(%r31)
	ld %r4, 16(%r31)
	xor %r3, %r3, %r4
	std %r3, 112(%r31)
	ld %r3, 120(%r31)
	ld %r4, 24(%r31)
	xor %r3, %r3, %r4
	std %r3, 120(%r31)
	ld %r3, 112(%r31)
	ld %r4, 64(%r31)
	xor %r3, %r3, %r4
	std %r3, 112(%r31)
	ld %r3, 120(%r31)
	ld %r4, 72(%r31)
	xor %r3, %r3, %r4
	std %r3, 120(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r7, %r31, 512
	addi %r5, %r31, 112
	li %r6, 1
	bl {vg_aes_encrypt_blocks}
	ld %r3, 112(%r31)
	ld %r4, 120(%r31)
	std %r3, 0(%r31)
	std %r4, 8(%r31)
	ld %r3, 0(%r31)
	ld %r4, 48(%r31)
	xor %r3, %r3, %r4
	std %r3, 0(%r31)
	ld %r3, 8(%r31)
	ld %r4, 56(%r31)
	xor %r3, %r3, %r4
	std %r3, 8(%r31)
	or %r3, %r31, %r31
	or %r4, %r20, %r20
	or %r5, %r19, %r19
228:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 228b
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

vg_aes_ocb_open:
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
	li %r0, 240
	ldbrx %r3, %r29, %r0
	li %r0, 248
	ldbrx %r4, %r29, %r0
	rldicl %r5, %r3, 1, 63
	li %r6, 0
	subf %r5, %r5, %r6
	li %r6, 135
	and %r5, %r5, %r6
	rldicr %r3, %r3, 1, 62
	rldicl %r6, %r4, 1, 63
	or %r3, %r3, %r6
	rldicr %r4, %r4, 1, 62
	xor %r4, %r4, %r5
	li %r0, 64
	stdbrx %r3, %r31, %r0
	li %r0, 72
	stdbrx %r4, %r31, %r0
	li %r0, 64
	ldbrx %r3, %r31, %r0
	li %r0, 72
	ldbrx %r4, %r31, %r0
	rldicl %r5, %r3, 1, 63
	li %r6, 0
	subf %r5, %r5, %r6
	li %r6, 135
	and %r5, %r5, %r6
	rldicr %r3, %r3, 1, 62
	rldicl %r6, %r4, 1, 63
	or %r3, %r3, %r6
	rldicr %r4, %r4, 1, 62
	xor %r4, %r4, %r5
	li %r0, 80
	stdbrx %r3, %r31, %r0
	li %r0, 88
	stdbrx %r4, %r31, %r0
	li %r0, 0
	std %r0, 32(%r31)
	std %r0, 40(%r31)
	li %r0, 0
	std %r0, 112(%r31)
	std %r0, 120(%r31)
	addi %r4, %r31, 127
	subf %r4, %r25, %r4
	li %r0, 1
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	or %r3, %r24, %r24
	or %r5, %r25, %r25
20:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	li %r0, 15
	and %r3, %r19, %r0
	rldicr %r3, %r3, 4, 59
	lbz %r4, 112(%r31)
	or %r4, %r4, %r3
	stb %r4, 112(%r31)
	lbz %r4, 127(%r31)
	li %r0, 63
	and %r3, %r4, %r0
	std %r3, 288(%r31)
	li %r0, 192
	and %r4, %r4, %r0
	stb %r4, 127(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r7, %r31, 512
	addi %r5, %r31, 112
	li %r6, 1
	bl {vg_aes_encrypt_blocks}
	li %r0, 112
	ldbrx %r3, %r31, %r0
	li %r0, 120
	ldbrx %r4, %r31, %r0
	rldicr %r5, %r3, 8, 55
	rldicl %r8, %r4, 8, 56
	or %r5, %r5, %r8
	xor %r5, %r5, %r3
	ld %r6, 288(%r31)
	li %r0, 1
	and %r7, %r6, %r0
	li %r8, 0
	subf %r7, %r7, %r8
	rldicr %r8, %r3, 1, 62
	rldicl %r9, %r4, 1, 63
	or %r8, %r8, %r9
	xor %r8, %r8, %r3
	and %r8, %r8, %r7
	xor %r3, %r3, %r8
	rldicr %r8, %r4, 1, 62
	rldicl %r9, %r5, 1, 63
	or %r8, %r8, %r9
	xor %r8, %r8, %r4
	and %r8, %r8, %r7
	xor %r4, %r4, %r8
	rldicr %r8, %r5, 1, 62
	xor %r8, %r8, %r5
	and %r8, %r8, %r7
	xor %r5, %r5, %r8
	rldicl %r7, %r6, 63, 1
	li %r0, 1
	and %r7, %r7, %r0
	li %r8, 0
	subf %r7, %r7, %r8
	rldicr %r8, %r3, 2, 61
	rldicl %r9, %r4, 2, 62
	or %r8, %r8, %r9
	xor %r8, %r8, %r3
	and %r8, %r8, %r7
	xor %r3, %r3, %r8
	rldicr %r8, %r4, 2, 61
	rldicl %r9, %r5, 2, 62
	or %r8, %r8, %r9
	xor %r8, %r8, %r4
	and %r8, %r8, %r7
	xor %r4, %r4, %r8
	rldicr %r8, %r5, 2, 61
	xor %r8, %r8, %r5
	and %r8, %r8, %r7
	xor %r5, %r5, %r8
	rldicl %r7, %r6, 62, 2
	li %r0, 1
	and %r7, %r7, %r0
	li %r8, 0
	subf %r7, %r7, %r8
	rldicr %r8, %r3, 4, 59
	rldicl %r9, %r4, 4, 60
	or %r8, %r8, %r9
	xor %r8, %r8, %r3
	and %r8, %r8, %r7
	xor %r3, %r3, %r8
	rldicr %r8, %r4, 4, 59
	rldicl %r9, %r5, 4, 60
	or %r8, %r8, %r9
	xor %r8, %r8, %r4
	and %r8, %r8, %r7
	xor %r4, %r4, %r8
	rldicr %r8, %r5, 4, 59
	xor %r8, %r8, %r5
	and %r8, %r8, %r7
	xor %r5, %r5, %r8
	rldicl %r7, %r6, 61, 3
	li %r0, 1
	and %r7, %r7, %r0
	li %r8, 0
	subf %r7, %r7, %r8
	rldicr %r8, %r3, 8, 55
	rldicl %r9, %r4, 8, 56
	or %r8, %r8, %r9
	xor %r8, %r8, %r3
	and %r8, %r8, %r7
	xor %r3, %r3, %r8
	rldicr %r8, %r4, 8, 55
	rldicl %r9, %r5, 8, 56
	or %r8, %r8, %r9
	xor %r8, %r8, %r4
	and %r8, %r8, %r7
	xor %r4, %r4, %r8
	rldicr %r8, %r5, 8, 55
	xor %r8, %r8, %r5
	and %r8, %r8, %r7
	xor %r5, %r5, %r8
	rldicl %r7, %r6, 60, 4
	li %r0, 1
	and %r7, %r7, %r0
	li %r8, 0
	subf %r7, %r7, %r8
	rldicr %r8, %r3, 16, 47
	rldicl %r9, %r4, 16, 48
	or %r8, %r8, %r9
	xor %r8, %r8, %r3
	and %r8, %r8, %r7
	xor %r3, %r3, %r8
	rldicr %r8, %r4, 16, 47
	rldicl %r9, %r5, 16, 48
	or %r8, %r8, %r9
	xor %r8, %r8, %r4
	and %r8, %r8, %r7
	xor %r4, %r4, %r8
	rldicr %r8, %r5, 16, 47
	xor %r8, %r8, %r5
	and %r8, %r8, %r7
	xor %r5, %r5, %r8
	rldicl %r7, %r6, 59, 5
	li %r0, 1
	and %r7, %r7, %r0
	li %r8, 0
	subf %r7, %r7, %r8
	rldicr %r8, %r3, 32, 31
	rldicl %r9, %r4, 32, 32
	or %r8, %r8, %r9
	xor %r8, %r8, %r3
	and %r8, %r8, %r7
	xor %r3, %r3, %r8
	rldicr %r8, %r4, 32, 31
	rldicl %r9, %r5, 32, 32
	or %r8, %r8, %r9
	xor %r8, %r8, %r4
	and %r8, %r8, %r7
	xor %r4, %r4, %r8
	rldicr %r8, %r5, 32, 31
	xor %r8, %r8, %r5
	and %r8, %r8, %r7
	xor %r5, %r5, %r8
	li %r0, 16
	stdbrx %r3, %r31, %r0
	li %r0, 24
	stdbrx %r4, %r31, %r0
	li %r0, 320
	stdbrx %r3, %r31, %r0
	li %r0, 328
	stdbrx %r4, %r31, %r0
	li %r0, 0
	std %r0, 48(%r31)
	std %r0, 56(%r31)
	li %r0, 0
	std %r0, 272(%r31)
	std %r0, 280(%r31)
	or %r24, %r21, %r21
	rldicl %r3, %r22, 60, 4
	std %r3, 304(%r31)
	li %r26, 1
	cmpldi %cr0, %r3, 0
	beq %cr0, 21f
23:
	ld %r3, 304(%r31)
	rldicl %r4, %r3, 61, 3
	cmpldi %cr0, %r4, 0
	beq %cr0, 24f
	li %r25, 8
	b 25f
24:
	or %r25, %r3, %r3
25:
	std %r25, 296(%r31)
	ld %r3, 304(%r31)
	subf %r3, %r25, %r3
	std %r3, 304(%r31)
	addi %r11, %r31, 384
26:
	ld %r3, 80(%r31)
	ld %r4, 88(%r31)
	std %r3, 96(%r31)
	std %r4, 104(%r31)
	or %r12, %r26, %r26
	li %r0, 1
	and %r5, %r12, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 27f
	b 28f
27:
29:
	li %r0, 96
	ldbrx %r3, %r31, %r0
	li %r0, 104
	ldbrx %r4, %r31, %r0
	rldicl %r5, %r3, 1, 63
	li %r6, 0
	subf %r5, %r5, %r6
	li %r6, 135
	and %r5, %r5, %r6
	rldicr %r3, %r3, 1, 62
	rldicl %r6, %r4, 1, 63
	or %r3, %r3, %r6
	rldicr %r4, %r4, 1, 62
	xor %r4, %r4, %r5
	li %r0, 96
	stdbrx %r3, %r31, %r0
	li %r0, 104
	stdbrx %r4, %r31, %r0
	rldicl %r12, %r12, 63, 1
	li %r0, 1
	and %r5, %r12, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 29b
28:
	ld %r3, 272(%r31)
	ld %r4, 96(%r31)
	xor %r3, %r3, %r4
	std %r3, 272(%r31)
	ld %r3, 280(%r31)
	ld %r4, 104(%r31)
	xor %r3, %r3, %r4
	std %r3, 280(%r31)
	ld %r3, 0(%r24)
	ld %r4, 272(%r31)
	xor %r3, %r3, %r4
	std %r3, 0(%r11)
	ld %r3, 8(%r24)
	ld %r4, 280(%r31)
	xor %r3, %r3, %r4
	std %r3, 8(%r11)
	addi %r11, %r11, 16
	addi %r24, %r24, 16
	addi %r26, %r26, 1
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 26b
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r7, %r31, 512
	addi %r5, %r31, 384
	ld %r6, 296(%r31)
	bl {vg_aes_encrypt_blocks}
	addi %r11, %r31, 384
	ld %r25, 296(%r31)
210:
	ld %r3, 48(%r31)
	ld %r4, 0(%r11)
	xor %r3, %r3, %r4
	std %r3, 48(%r31)
	ld %r3, 56(%r31)
	ld %r4, 8(%r11)
	xor %r3, %r3, %r4
	std %r3, 56(%r31)
	addi %r11, %r11, 16
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 210b
	ld %r3, 304(%r31)
	cmpldi %cr0, %r3, 0
	bne %cr0, 23b
	b 22f
21:
22:
	li %r0, 15
	and %r25, %r22, %r0
	cmpldi %cr0, %r25, 0
	beq %cr0, 211f
	ld %r3, 272(%r31)
	ld %r4, 240(%r29)
	xor %r3, %r3, %r4
	std %r3, 272(%r31)
	ld %r3, 280(%r31)
	ld %r4, 248(%r29)
	xor %r3, %r3, %r4
	std %r3, 280(%r31)
	li %r0, 0
	std %r0, 384(%r31)
	std %r0, 392(%r31)
	addi %r4, %r31, 384
	or %r3, %r24, %r24
	or %r5, %r25, %r25
213:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 213b
	li %r0, 128
	stb %r0, 0(%r4)
	ld %r3, 384(%r31)
	ld %r4, 272(%r31)
	xor %r3, %r3, %r4
	std %r3, 384(%r31)
	ld %r3, 392(%r31)
	ld %r4, 280(%r31)
	xor %r3, %r3, %r4
	std %r3, 392(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r7, %r31, 512
	addi %r5, %r31, 384
	li %r6, 1
	bl {vg_aes_encrypt_blocks}
	ld %r3, 48(%r31)
	ld %r4, 384(%r31)
	xor %r3, %r3, %r4
	std %r3, 48(%r31)
	ld %r3, 56(%r31)
	ld %r4, 392(%r31)
	xor %r3, %r3, %r4
	std %r3, 56(%r31)
	b 212f
211:
212:
	rldicl %r3, %r23, 60, 4
	cmpldi %cr0, %r3, 0
	beq %cr0, 214f
	or %r24, %r27, %r27
	rldicl %r25, %r23, 60, 4
	li %r26, 1
216:
	ld %r3, 80(%r31)
	ld %r4, 88(%r31)
	std %r3, 96(%r31)
	std %r4, 104(%r31)
	or %r12, %r26, %r26
	li %r0, 1
	and %r5, %r12, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 217f
	b 218f
217:
219:
	li %r0, 96
	ldbrx %r3, %r31, %r0
	li %r0, 104
	ldbrx %r4, %r31, %r0
	rldicl %r5, %r3, 1, 63
	li %r6, 0
	subf %r5, %r5, %r6
	li %r6, 135
	and %r5, %r5, %r6
	rldicr %r3, %r3, 1, 62
	rldicl %r6, %r4, 1, 63
	or %r3, %r3, %r6
	rldicr %r4, %r4, 1, 62
	xor %r4, %r4, %r5
	li %r0, 96
	stdbrx %r3, %r31, %r0
	li %r0, 104
	stdbrx %r4, %r31, %r0
	rldicl %r12, %r12, 63, 1
	li %r0, 1
	and %r5, %r12, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 219b
218:
	ld %r3, 16(%r31)
	ld %r4, 96(%r31)
	xor %r3, %r3, %r4
	std %r3, 16(%r31)
	ld %r3, 24(%r31)
	ld %r4, 104(%r31)
	xor %r3, %r3, %r4
	std %r3, 24(%r31)
	ld %r3, 0(%r24)
	ld %r4, 16(%r31)
	xor %r3, %r3, %r4
	std %r3, 0(%r24)
	ld %r3, 8(%r24)
	ld %r4, 24(%r31)
	xor %r3, %r3, %r4
	std %r3, 8(%r24)
	addi %r24, %r24, 16
	addi %r26, %r26, 1
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 216b
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r7, %r31, 512
	or %r5, %r27, %r27
	rldicl %r6, %r23, 60, 4
	bl {vg_aes_decrypt_blocks}
	ld %r3, 320(%r31)
	ld %r4, 328(%r31)
	std %r3, 16(%r31)
	std %r4, 24(%r31)
	or %r24, %r27, %r27
	rldicl %r25, %r23, 60, 4
	li %r26, 1
220:
	ld %r3, 80(%r31)
	ld %r4, 88(%r31)
	std %r3, 96(%r31)
	std %r4, 104(%r31)
	or %r12, %r26, %r26
	li %r0, 1
	and %r5, %r12, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 221f
	b 222f
221:
223:
	li %r0, 96
	ldbrx %r3, %r31, %r0
	li %r0, 104
	ldbrx %r4, %r31, %r0
	rldicl %r5, %r3, 1, 63
	li %r6, 0
	subf %r5, %r5, %r6
	li %r6, 135
	and %r5, %r5, %r6
	rldicr %r3, %r3, 1, 62
	rldicl %r6, %r4, 1, 63
	or %r3, %r3, %r6
	rldicr %r4, %r4, 1, 62
	xor %r4, %r4, %r5
	li %r0, 96
	stdbrx %r3, %r31, %r0
	li %r0, 104
	stdbrx %r4, %r31, %r0
	rldicl %r12, %r12, 63, 1
	li %r0, 1
	and %r5, %r12, %r0
	cmpldi %cr0, %r5, 0
	beq %cr0, 223b
222:
	ld %r3, 16(%r31)
	ld %r4, 96(%r31)
	xor %r3, %r3, %r4
	std %r3, 16(%r31)
	ld %r3, 24(%r31)
	ld %r4, 104(%r31)
	xor %r3, %r3, %r4
	std %r3, 24(%r31)
	ld %r3, 0(%r24)
	ld %r4, 16(%r31)
	xor %r3, %r3, %r4
	std %r3, 0(%r24)
	ld %r3, 8(%r24)
	ld %r4, 24(%r31)
	xor %r3, %r3, %r4
	std %r3, 8(%r24)
	ld %r3, 32(%r31)
	ld %r4, 0(%r24)
	xor %r3, %r3, %r4
	std %r3, 32(%r31)
	ld %r3, 40(%r31)
	ld %r4, 8(%r24)
	xor %r3, %r3, %r4
	std %r3, 40(%r31)
	addi %r24, %r24, 16
	addi %r26, %r26, 1
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 220b
	b 215f
214:
215:
	li %r0, 15
	and %r25, %r23, %r0
	subf %r24, %r25, %r23
	add %r24, %r24, %r27
	cmpldi %cr0, %r25, 0
	beq %cr0, 224f
	ld %r3, 16(%r31)
	ld %r4, 240(%r29)
	xor %r3, %r3, %r4
	std %r3, 16(%r31)
	ld %r3, 24(%r31)
	ld %r4, 248(%r29)
	xor %r3, %r3, %r4
	std %r3, 24(%r31)
	ld %r3, 16(%r31)
	ld %r4, 24(%r31)
	std %r3, 112(%r31)
	std %r4, 120(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r7, %r31, 512
	addi %r5, %r31, 112
	li %r6, 1
	bl {vg_aes_encrypt_blocks}
	addi %r3, %r31, 112
	or %r4, %r24, %r24
	or %r5, %r25, %r25
226:
	lbz %r0, 0(%r4)
	lbz %r6, 0(%r3)
	xor %r0, %r0, %r6
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 226b
	li %r0, 0
	std %r0, 256(%r31)
	std %r0, 264(%r31)
	addi %r4, %r31, 256
	or %r3, %r24, %r24
	or %r5, %r25, %r25
227:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 227b
	li %r0, 128
	stb %r0, 0(%r4)
	ld %r3, 32(%r31)
	ld %r4, 256(%r31)
	xor %r3, %r3, %r4
	std %r3, 32(%r31)
	ld %r3, 40(%r31)
	ld %r4, 264(%r31)
	xor %r3, %r3, %r4
	std %r3, 40(%r31)
	b 225f
224:
225:
	ld %r3, 32(%r31)
	ld %r4, 40(%r31)
	std %r3, 112(%r31)
	std %r4, 120(%r31)
	ld %r3, 112(%r31)
	ld %r4, 16(%r31)
	xor %r3, %r3, %r4
	std %r3, 112(%r31)
	ld %r3, 120(%r31)
	ld %r4, 24(%r31)
	xor %r3, %r3, %r4
	std %r3, 120(%r31)
	ld %r3, 112(%r31)
	ld %r4, 64(%r31)
	xor %r3, %r3, %r4
	std %r3, 112(%r31)
	ld %r3, 120(%r31)
	ld %r4, 72(%r31)
	xor %r3, %r3, %r4
	std %r3, 120(%r31)
	or %r3, %r29, %r29
	or %r4, %r28, %r28
	addi %r7, %r31, 512
	addi %r5, %r31, 112
	li %r6, 1
	bl {vg_aes_encrypt_blocks}
	ld %r3, 112(%r31)
	ld %r4, 120(%r31)
	std %r3, 256(%r31)
	std %r4, 264(%r31)
	ld %r3, 256(%r31)
	ld %r4, 48(%r31)
	xor %r3, %r3, %r4
	std %r3, 256(%r31)
	ld %r3, 264(%r31)
	ld %r4, 56(%r31)
	xor %r3, %r3, %r4
	std %r3, 264(%r31)
	li %r0, 0
	std %r0, 0(%r31)
	std %r0, 8(%r31)
	or %r3, %r20, %r20
	or %r4, %r31, %r31
	or %r5, %r19, %r19
228:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 228b
	li %r0, 0
	std %r0, 336(%r31)
	std %r0, 344(%r31)
	addi %r3, %r31, 256
	addi %r4, %r31, 336
	or %r5, %r19, %r19
229:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 229b
	ld %r3, 0(%r31)
	ld %r4, 336(%r31)
	xor %r3, %r3, %r4
	ld %r4, 8(%r31)
	ld %r5, 344(%r31)
	xor %r4, %r4, %r5
	or %r3, %r3, %r4
	li %r4, 0
	subf %r4, %r3, %r4
	or %r3, %r3, %r4
	rldicl %r3, %r3, 1, 63
	li %r4, 1
	subf %r3, %r3, %r4
	or %r24, %r27, %r27
	or %r25, %r23, %r23
	li %r4, 0
	subf %r7, %r3, %r4
	cmpldi %cr0, %r25, 0
	beq %cr0, 230f
232:
	lbz %r4, 0(%r24)
	and %r4, %r4, %r7
	stb %r4, 0(%r24)
	addi %r24, %r24, 1
	addi %r25, %r25, -1
	cmpldi %cr0, %r25, 0
	bne %cr0, 232b
	b 231f
230:
231:
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
