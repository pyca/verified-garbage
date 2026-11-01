// The functions of `src/rsa_oaep_sha512_mgf1_sha512.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_oaep_sha512_mgf1_sha512_encrypt_precomputed:
	stdu %r1, -256(%r1)
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r14, 376(%r12)
	or %r15, %r6, %r6
	or %r16, %r3, %r3
	or %r17, %r7, %r7
	or %r18, %r8, %r8
	or %r19, %r9, %r9
	or %r20, %r10, %r10
	ld %r21, 392(%r12)
	ld %r22, 400(%r12)
	ld %r23, 384(%r12)
	ld %r9, 352(%r12)
	ld %r10, 360(%r12)
	ld %r11, 368(%r12)
	li %r3, 130
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 20f
	li %r3, 130
	subf %r4, %r3, %r15
	subf %r4, %r10, %r4
	rldicl %r4, %r4, 1, 63
	rldicl %r3, %r10, 1, 63
	or %r3, %r3, %r4
	cmpldi %cr0, %r3, 0
	bne %cr0, 22f
	addi %r4, %r14, 0
	li %r5, 1024
	li %r6, 0
24:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 24b
	or %r4, %r11, %r11
	addi %r5, %r14, 1
	li %r6, 64
25:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 25b
	add %r5, %r14, %r15
	subf %r5, %r10, %r5
	addi %r5, %r5, -1
	li %r7, 1
	stb %r7, 0(%r5)
	addi %r5, %r5, 1
	or %r4, %r9, %r9
	or %r6, %r10, %r10
	cmpldi %cr0, %r6, 0
	bne %cr0, 26f
	b 27f
26:
28:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 28b
27:
	addi %r3, %r14, 1024
	bl {vg_sha512_init}
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r19, %r19
	or %r6, %r20, %r20
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	addi %r3, %r14, 1024
	or %r4, %r20, %r20
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	bl {vg_sha512_finalize_scratch}
	addi %r4, %r14, 1280
	addi %r5, %r14, 65
	li %r6, 64
29:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 29b
	addi %r24, %r14, 1
	li %r25, 64
	addi %r26, %r14, 65
	addi %r27, %r15, -65
	li %r28, 0
	li %r29, 0
210:
	addi %r3, %r14, 1024
	bl {vg_sha512_init}
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	bl {vg_sha512_finalize_scratch}
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	li %r9, 64
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
211:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 211b
	addi %r28, %r28, 1
	addi %r29, %r29, 64
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 210b
	addi %r24, %r14, 65
	addi %r25, %r15, -65
	addi %r26, %r14, 1
	li %r27, 64
	li %r28, 0
	li %r29, 0
212:
	addi %r3, %r14, 1024
	bl {vg_sha512_init}
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	bl {vg_sha512_finalize_scratch}
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	li %r9, 64
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
213:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 213b
	addi %r28, %r28, 1
	addi %r29, %r29, 64
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 212b
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r23, -1024
	std %r5, 104(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r21, %r21
	or %r6, %r22, %r22
	or %r7, %r17, %r17
	or %r8, %r18, %r18
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	b 23f
22:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
214:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 214b
	li %r3, 0
23:
	b 21f
20:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
215:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
	li %r3, 0
21:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
	addi %r1, %r1, 256
	blr

vg_rsa_oaep_sha512_mgf1_sha512_decrypt:
	stdu %r1, -256(%r1)
	addi %r12, %r1, 0
	std %r14, 112(%r12)
	std %r15, 120(%r12)
	std %r16, 128(%r12)
	std %r17, 136(%r12)
	std %r18, 144(%r12)
	std %r19, 152(%r12)
	std %r20, 160(%r12)
	std %r21, 168(%r12)
	std %r22, 176(%r12)
	std %r23, 184(%r12)
	std %r24, 192(%r12)
	std %r25, 200(%r12)
	std %r26, 208(%r12)
	std %r27, 216(%r12)
	std %r28, 224(%r12)
	std %r29, 232(%r12)
	mflr %r0
	std %r0, 240(%r12)
	ld %r14, 456(%r12)
	or %r15, %r7, %r7
	or %r16, %r3, %r3
	or %r17, %r5, %r5
	ld %r18, 424(%r12)
	ld %r19, 432(%r12)
	stdu %r1, -192(%r1)
	addi %r12, %r1, 0
	std %r10, 96(%r12)
	ld %r0, 544(%r12)
	std %r0, 104(%r12)
	ld %r0, 552(%r12)
	std %r0, 112(%r12)
	ld %r0, 560(%r12)
	std %r0, 120(%r12)
	ld %r0, 568(%r12)
	std %r0, 128(%r12)
	ld %r0, 576(%r12)
	std %r0, 136(%r12)
	ld %r0, 584(%r12)
	std %r0, 144(%r12)
	ld %r0, 592(%r12)
	std %r0, 152(%r12)
	ld %r0, 600(%r12)
	std %r0, 160(%r12)
	ld %r0, 608(%r12)
	std %r0, 168(%r12)
	li %r0, 8192
	add %r0, %r14, %r0
	std %r0, 176(%r12)
	ld %r11, 656(%r12)
	addi %r11, %r11, -1024
	std %r11, 184(%r12)
	addi %r3, %r14, 0
	or %r4, %r15, %r15
	or %r5, %r6, %r6
	or %r6, %r15, %r15
	or %r7, %r8, %r8
	or %r8, %r9, %r9
	ld %r9, 632(%r12)
	or %r10, %r15, %r15
	bl {vg_rsa_private_checked}
	addi %r1, %r1, 192
	rlwinm %r20, %r3, 0, 0, 31
	li %r3, 130
	subf %r3, %r3, %r15
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 20f
	addi %r24, %r14, 65
	addi %r25, %r15, -65
	addi %r26, %r14, 1
	li %r27, 64
	li %r28, 0
	li %r29, 0
22:
	addi %r3, %r14, 1024
	bl {vg_sha512_init}
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	bl {vg_sha512_finalize_scratch}
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	li %r9, 64
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
23:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 23b
	addi %r28, %r28, 1
	addi %r29, %r29, 64
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 22b
	addi %r24, %r14, 1
	li %r25, 64
	addi %r26, %r14, 65
	addi %r27, %r15, -65
	li %r28, 0
	li %r29, 0
24:
	addi %r3, %r14, 1024
	bl {vg_sha512_init}
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r24, %r24
	or %r6, %r25, %r25
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	addi %r5, %r14, 1344
	or %r8, %r28, %r28
	stb %r8, 3(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 2(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 1(%r5)
	rldicl %r8, %r8, 56, 8
	stb %r8, 0(%r5)
	addi %r3, %r14, 1024
	or %r4, %r25, %r25
	li %r6, 4
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	addi %r3, %r14, 1024
	addi %r4, %r25, 4
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	bl {vg_sha512_finalize_scratch}
	addi %r11, %r14, 1280
	add %r12, %r26, %r29
	subf %r8, %r29, %r27
	li %r9, 64
	subf %r10, %r9, %r8
	rldicl %r6, %r10, 1, 63
	li %r7, 0
	subf %r6, %r6, %r7
	and %r10, %r10, %r6
	add %r9, %r9, %r10
25:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 25b
	addi %r28, %r28, 1
	addi %r29, %r29, 64
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	addi %r3, %r14, 1024
	bl {vg_sha512_init}
	addi %r3, %r14, 1024
	li %r4, 0
	or %r5, %r18, %r18
	or %r6, %r19, %r19
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	addi %r3, %r14, 1024
	or %r4, %r19, %r19
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	bl {vg_sha512_finalize_scratch}
	addi %r4, %r14, 65
	addi %r5, %r14, 1280
	lbz %r24, 0(%r14)
	li %r6, 64
26:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 26b
	addi %r4, %r14, 129
	addi %r5, %r15, -129
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r25, 0
27:
	lbz %r10, 0(%r4)
	addi %r8, %r10, -1
	rldicl %r8, %r8, 1, 63
	li %r9, 1
	xor %r9, %r10, %r9
	addi %r9, %r9, -1
	rldicl %r9, %r9, 1, 63
	or %r8, %r8, %r9
	addi %r8, %r8, -1
	and %r8, %r8, %r7
	or %r24, %r24, %r8
	li %r3, 0
	subf %r3, %r9, %r3
	and %r8, %r6, %r7
	and %r8, %r8, %r3
	or %r25, %r25, %r8
	addi %r9, %r9, -1
	and %r7, %r7, %r9
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 27b
	or %r24, %r24, %r7
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
28:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 28b
	addi %r4, %r14, 129
	addi %r5, %r15, -129
	or %r6, %r5, %r5
	addi %r5, %r14, 2560
29:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 29b
	addi %r8, %r25, 1
	li %r9, 1
	li %r10, 10
210:
	addi %r4, %r14, 2560
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r15, %r15
211:
	lbz %r11, 0(%r4)
	lbz %r3, 0(%r5)
	xor %r3, %r3, %r11
	and %r3, %r3, %r6
	xor %r11, %r11, %r3
	stb %r11, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r7, %r7, -1
	cmpldi %cr0, %r7, 0
	bne %cr0, 211b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 210b
	li %r4, 1
	xor %r4, %r20, %r4
	addi %r4, %r4, -1
	rldicl %r4, %r4, 1, 63
	li %r5, 0
	subf %r5, %r24, %r5
	or %r5, %r5, %r24
	rldicl %r5, %r5, 1, 63
	li %r6, 1
	xor %r5, %r5, %r6
	and %r4, %r4, %r5
	li %r26, 0
	subf %r26, %r4, %r26
	addi %r4, %r14, 2560
	or %r5, %r16, %r16
	or %r6, %r15, %r15
212:
	lbz %r7, 0(%r4)
	and %r7, %r7, %r26
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 212b
	addi %r4, %r15, -130
	subf %r4, %r25, %r4
	and %r4, %r4, %r26
	std %r4, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
	li %r4, 1
	and %r4, %r26, %r4
	or %r3, %r3, %r4
	b 21f
20:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
213:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 213b
	std %r6, 0(%r17)
	li %r4, 2
	xor %r3, %r20, %r4
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	add %r3, %r3, %r3
21:
	addi %r12, %r1, 0
	ld %r0, 240(%r12)
	mtlr %r0
	ld %r14, 112(%r12)
	ld %r15, 120(%r12)
	ld %r16, 128(%r12)
	ld %r17, 136(%r12)
	ld %r18, 144(%r12)
	ld %r19, 152(%r12)
	ld %r20, 160(%r12)
	ld %r21, 168(%r12)
	ld %r22, 176(%r12)
	ld %r23, 184(%r12)
	ld %r24, 192(%r12)
	ld %r25, 200(%r12)
	ld %r26, 208(%r12)
	ld %r27, 216(%r12)
	ld %r28, 224(%r12)
	ld %r29, 232(%r12)
	addi %r1, %r1, 256
	blr
