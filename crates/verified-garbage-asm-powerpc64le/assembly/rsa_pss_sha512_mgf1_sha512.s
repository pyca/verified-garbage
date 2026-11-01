// The functions of `src/rsa_pss_sha512_mgf1_sha512.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pss_sha512_mgf1_sha512_verify_precomputed:
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
	ld %r20, 352(%r12)
	rlwinm %r20, %r20, 0, 0, 31
	ld %r14, 360(%r12)
	ld %r27, 368(%r12)
	ld %r22, 376(%r12)
	ld %r23, 384(%r12)
	or %r15, %r4, %r4
	or %r16, %r7, %r7
	or %r19, %r10, %r10
	or %r24, %r5, %r5
	or %r25, %r6, %r6
	or %r26, %r8, %r8
	lbz %r9, 0(%r3)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r17, %r11, 1, 63
	li %r11, 0
	subf %r11, %r17, %r11
	li %r8, 255
	and %r11, %r11, %r8
	or %r18, %r10, %r11
	subf %r21, %r17, %r15
	addi %r21, %r21, -65
	cmpldi %cr0, %r9, 0
	beq %cr0, 20f
	subf %r3, %r17, %r15
	addi %r3, %r3, -66
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 22f
	cmpldi %cr0, %r20, 0
	beq %cr0, 24f
	li %r4, 0
	b 25f
24:
	or %r4, %r19, %r19
25:
	subf %r3, %r17, %r15
	addi %r3, %r3, -66
	subf %r3, %r4, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r4, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 26f
	addi %r12, %r1, 0
	li %r4, 8192
	add %r4, %r14, %r4
	std %r4, 96(%r12)
	addi %r5, %r27, -1024
	std %r5, 104(%r12)
	addi %r3, %r14, 0
	or %r4, %r15, %r15
	or %r5, %r22, %r22
	or %r6, %r23, %r23
	or %r7, %r24, %r24
	or %r8, %r25, %r25
	or %r9, %r26, %r26
	or %r10, %r15, %r15
	bl {vg_rsa_public_precomputed_checked}
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r5, 0(%r4)
	li %r6, 188
	xor %r5, %r5, %r6
	add %r7, %r14, %r17
	lbz %r6, 0(%r7)
	li %r8, 255
	xor %r8, %r8, %r18
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	lbz %r6, 0(%r14)
	li %r8, 0
	subf %r8, %r17, %r8
	and %r6, %r6, %r8
	or %r5, %r5, %r6
	stb %r5, 0(%r4)
	add %r26, %r14, %r17
	or %r27, %r21, %r21
	add %r24, %r26, %r21
	li %r25, 64
	li %r28, 0
	li %r29, 0
28:
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
29:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 29b
	addi %r28, %r28, 1
	addi %r29, %r29, 64
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 28b
	add %r4, %r14, %r17
	lbz %r5, 0(%r4)
	and %r5, %r5, %r18
	stb %r5, 0(%r4)
	add %r4, %r14, %r17
	or %r5, %r21, %r21
	li %r6, 0
	li %r7, 0
	addi %r7, %r7, -1
	li %r8, 0
	li %r9, 0
210:
	lbz %r10, 0(%r4)
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	addi %r12, %r11, -1
	and %r12, %r12, %r7
	and %r3, %r6, %r12
	or %r8, %r8, %r3
	and %r3, %r10, %r12
	or %r9, %r9, %r3
	li %r3, 0
	subf %r3, %r11, %r3
	and %r7, %r7, %r3
	addi %r4, %r4, 1
	addi %r6, %r6, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 210b
	add %r4, %r14, %r15
	addi %r4, %r4, -1
	lbz %r24, 0(%r4)
	li %r3, 1
	xor %r9, %r9, %r3
	or %r24, %r24, %r9
	subf %r25, %r8, %r21
	addi %r25, %r25, -1
	cmpldi %cr0, %r20, 0
	beq %cr0, 211f
	b 212f
211:
	xor %r3, %r25, %r19
	or %r24, %r24, %r3
212:
	cmpldi %cr0, %r20, 0
	beq %cr0, 213f
	addi %r4, %r14, 2560
	li %r5, 2048
	li %r6, 0
215:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 215b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 64
216:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 216b
	add %r4, %r14, %r17
	addi %r5, %r14, 2632
	or %r6, %r21, %r21
217:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 217b
	addi %r8, %r8, 1
	li %r9, 1
	li %r10, 10
218:
	addi %r4, %r14, 2632
	add %r5, %r4, %r9
	li %r6, 1
	and %r6, %r8, %r6
	li %r7, 0
	subf %r6, %r6, %r7
	or %r7, %r21, %r21
219:
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
	bne %cr0, 219b
	rldicl %r8, %r8, 63, 1
	add %r9, %r9, %r9
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 218b
	addi %r3, %r14, 1024
	bl {vg_sha512_init}
	li %r4, 0
	addi %r5, %r14, 2560
	li %r6, 72
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	li %r26, 0
	or %r27, %r21, %r21
220:
	addi %r4, %r14, 1024
	addi %r5, %r14, 4608
	li %r6, 192
221:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 221b
	addi %r4, %r26, 72
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	bl {vg_sha512_finalize_scratch}
	xor %r3, %r26, %r25
	addi %r3, %r3, -1
	rldicl %r3, %r3, 1, 63
	li %r4, 0
	subf %r3, %r3, %r4
	addi %r4, %r14, 1280
	addi %r5, %r14, 4800
	li %r6, 64
222:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	and %r7, %r7, %r3
	xor %r8, %r8, %r7
	stb %r8, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 222b
	addi %r4, %r14, 4608
	addi %r5, %r14, 1024
	li %r6, 192
223:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 223b
	addi %r4, %r26, 72
	addi %r5, %r14, 2632
	add %r5, %r5, %r26
	li %r6, 1
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	addi %r26, %r26, 1
	addi %r27, %r27, -1
	cmpldi %cr0, %r27, 0
	bne %cr0, 220b
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 4800
	li %r6, 64
224:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 224b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
	b 214f
213:
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
225:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 225b
	or %r4, %r16, %r16
	addi %r5, %r14, 2568
	li %r6, 64
226:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 226b
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	subf %r4, %r19, %r4
	addi %r5, %r14, 2632
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 227f
	b 228f
227:
229:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 229b
228:
	addi %r3, %r14, 1024
	bl {vg_sha512_init}
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 72
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	addi %r4, %r19, 72
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	bl {vg_sha512_finalize_scratch}
	add %r4, %r14, %r17
	add %r4, %r4, %r21
	addi %r5, %r14, 1280
	li %r6, 64
230:
	lbz %r7, 0(%r4)
	lbz %r8, 0(%r5)
	xor %r7, %r7, %r8
	or %r24, %r24, %r7
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 230b
	addi %r3, %r24, -1
	rldicl %r3, %r3, 1, 63
214:
	b 27f
26:
	li %r3, 0
27:
	b 23f
22:
	li %r3, 0
23:
	b 21f
20:
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

vg_rsa_pss_sha512_mgf1_sha512_sign:
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
	ld %r14, 440(%r12)
	or %r15, %r6, %r6
	or %r16, %r3, %r3
	or %r17, %r9, %r9
	or %r18, %r10, %r10
	ld %r19, 432(%r12)
	or %r20, %r5, %r5
	or %r21, %r7, %r7
	or %r22, %r8, %r8
	lbz %r9, 0(%r5)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	or %r23, %r11, %r11
	cmpldi %cr0, %r9, 0
	beq %cr0, 20f
	subf %r3, %r23, %r15
	addi %r3, %r3, -66
	rldicl %r3, %r3, 1, 63
	cmpldi %cr0, %r3, 0
	bne %cr0, 22f
	subf %r3, %r23, %r15
	addi %r3, %r3, -66
	subf %r3, %r19, %r3
	rldicl %r3, %r3, 1, 63
	rldicl %r5, %r19, 1, 63
	or %r3, %r3, %r5
	cmpldi %cr0, %r3, 0
	bne %cr0, 24f
	addi %r4, %r14, 2560
	li %r5, 8
	li %r6, 0
26:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 26b
	addi %r12, %r1, 0
	ld %r4, 416(%r12)
	addi %r5, %r14, 2568
	li %r6, 64
27:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 27b
	addi %r5, %r14, 2632
	addi %r12, %r1, 0
	ld %r4, 424(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 28f
	b 29f
28:
210:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 210b
29:
	addi %r3, %r14, 1024
	bl {vg_sha512_init}
	li %r4, 0
	addi %r5, %r14, 2560
	addi %r6, %r19, 72
	addi %r3, %r14, 1024
	addi %r7, %r14, 1352
	bl {vg_sha512_update_scratch}
	addi %r4, %r19, 72
	addi %r3, %r14, 1024
	addi %r5, %r14, 1280
	addi %r6, %r14, 1352
	bl {vg_sha512_finalize_scratch}
	addi %r4, %r14, 0
	or %r5, %r15, %r15
	li %r6, 0
211:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 211b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	subf %r4, %r19, %r4
	addi %r4, %r4, -66
	li %r5, 1
	stb %r5, 0(%r4)
	addi %r5, %r4, 1
	addi %r12, %r1, 0
	ld %r4, 424(%r12)
	or %r6, %r19, %r19
	cmpldi %cr0, %r6, 0
	bne %cr0, 212f
	b 213f
212:
214:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 214b
213:
	addi %r4, %r14, 1280
	addi %r5, %r14, 0
	add %r5, %r5, %r15
	addi %r5, %r5, -65
	li %r6, 64
215:
	lbz %r7, 0(%r4)
	stb %r7, 0(%r5)
	addi %r4, %r4, 1
	addi %r5, %r5, 1
	addi %r6, %r6, -1
	cmpldi %cr0, %r6, 0
	bne %cr0, 215b
	addi %r4, %r14, 0
	add %r4, %r4, %r15
	addi %r4, %r4, -1
	li %r5, 188
	stb %r5, 0(%r4)
	addi %r24, %r14, 0
	add %r24, %r24, %r15
	addi %r24, %r24, -65
	li %r25, 64
	addi %r26, %r14, 0
	add %r26, %r26, %r23
	subf %r27, %r23, %r15
	addi %r27, %r27, -65
	li %r28, 0
	li %r29, 0
216:
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
217:
	lbz %r10, 0(%r11)
	lbz %r8, 0(%r12)
	xor %r8, %r8, %r10
	stb %r8, 0(%r12)
	addi %r11, %r11, 1
	addi %r12, %r12, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 217b
	addi %r28, %r28, 1
	addi %r29, %r29, 64
	subf %r12, %r27, %r29
	rldicl %r12, %r12, 1, 63
	cmpldi %cr0, %r12, 0
	bne %cr0, 216b
	lbz %r9, 0(%r20)
	rldicl %r10, %r9, 63, 1
	rldicl %r11, %r10, 63, 1
	or %r10, %r10, %r11
	rldicl %r11, %r10, 62, 2
	or %r10, %r10, %r11
	rldicl %r11, %r10, 60, 4
	or %r10, %r10, %r11
	addi %r11, %r10, -1
	rldicl %r11, %r11, 1, 63
	li %r8, 0
	subf %r8, %r11, %r8
	li %r7, 255
	and %r8, %r8, %r7
	or %r10, %r10, %r8
	addi %r4, %r14, 0
	add %r4, %r4, %r23
	lbz %r5, 0(%r4)
	and %r5, %r5, %r10
	stb %r5, 0(%r4)
	stdu %r1, -192(%r1)
	addi %r12, %r1, 0
	std %r17, 96(%r12)
	std %r18, 104(%r12)
	ld %r0, 544(%r12)
	std %r0, 112(%r12)
	ld %r0, 552(%r12)
	std %r0, 120(%r12)
	ld %r0, 560(%r12)
	std %r0, 128(%r12)
	ld %r0, 568(%r12)
	std %r0, 136(%r12)
	ld %r0, 576(%r12)
	std %r0, 144(%r12)
	ld %r0, 584(%r12)
	std %r0, 152(%r12)
	ld %r0, 592(%r12)
	std %r0, 160(%r12)
	ld %r0, 600(%r12)
	std %r0, 168(%r12)
	li %r0, 8192
	add %r0, %r14, %r0
	std %r0, 176(%r12)
	ld %r11, 640(%r12)
	addi %r11, %r11, -1024
	std %r11, 184(%r12)
	or %r3, %r16, %r16
	or %r4, %r15, %r15
	or %r5, %r20, %r20
	or %r6, %r15, %r15
	or %r7, %r21, %r21
	or %r8, %r22, %r22
	addi %r9, %r14, 0
	or %r10, %r15, %r15
	bl {vg_rsa_private_checked}
	addi %r1, %r1, 192
	b 25f
24:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
218:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 218b
	li %r3, 0
25:
	b 23f
22:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
219:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 219b
	li %r3, 0
23:
	b 21f
20:
	or %r4, %r16, %r16
	or %r5, %r15, %r15
	li %r6, 0
220:
	stb %r6, 0(%r4)
	addi %r4, %r4, 1
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 220b
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
