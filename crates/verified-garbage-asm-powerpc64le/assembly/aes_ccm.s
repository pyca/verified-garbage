// The functions of `src/aes_ccm.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ccm_seal:
	stdu %r1, -2688(%r1)
	addi %r12, %r1, 0
	ld %r0, 2784(%r12)
	std %r0, 96(%r12)
	ld %r0, 2792(%r12)
	std %r0, 104(%r12)
	addi %r0, %r12, 120
	std %r0, 112(%r12)
	addi %r12, %r1, 0
	ld %r11, 112(%r12)
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
	std %r14, 128(%r11)
	std %r0, 208(%r11)
	or %r14, %r11, %r11
	ld %r15, 104(%r12)
	ld %r11, 96(%r12)
	or %r16, %r3, %r3
	or %r17, %r4, %r4
	std %r7, 216(%r14)
	std %r8, 224(%r14)
	std %r6, 232(%r14)
	std %r11, 240(%r14)
	or %r22, %r9, %r9
	or %r23, %r10, %r10
	li %r0, 0
	std %r0, 48(%r14)
	std %r0, 56(%r14)
	li %r9, 14
	subf %r9, %r6, %r9
	stb %r9, 48(%r14)
	or %r3, %r5, %r5
	addi %r9, %r14, 49
	or %r4, %r6, %r6
20:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 20b
	ld %r18, 216(%r14)
	ld %r19, 224(%r14)
	addi %r9, %r15, -2
	rldicr %r9, %r9, 2, 61
	ld %r10, 232(%r14)
	li %r11, 14
	subf %r11, %r10, %r11
	add %r9, %r9, %r11
	cmpldi %cr0, %r19, 0
	beq %cr0, 21f
	addi %r9, %r9, 64
	b 22f
21:
22:
	ld %r10, 48(%r14)
	ld %r11, 56(%r14)
	std %r10, 32(%r14)
	std %r11, 40(%r14)
	stb %r9, 32(%r14)
	li %r11, 40
	ldbrx %r12, %r14, %r11
	or %r12, %r12, %r23
	stdbrx %r12, %r14, %r11
	li %r0, 0
	std %r0, 0(%r14)
	std %r0, 8(%r14)
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 0
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	li %r7, 1
	bl {vg_cmac_aes_update}
	cmpldi %cr0, %r19, 0
	beq %cr0, 23f
	li %r0, 0
	std %r0, 32(%r14)
	std %r0, 40(%r14)
	rldicl %r9, %r19, 32, 32
	cmpldi %cr0, %r9, 0
	beq %cr0, 25f
	li %r9, 255
	stb %r9, 32(%r14)
	stb %r9, 33(%r14)
	li %r10, 34
	stdbrx %r19, %r14, %r10
	li %r20, 10
	b 26f
25:
	rldicl %r9, %r19, 56, 8
	addi %r9, %r9, -255
	rldicl %r9, %r9, 1, 63
	cmpldi %cr0, %r9, 0
	beq %cr0, 27f
	rldicr %r9, %r19, 48, 15
	li %r10, 32
	stdbrx %r9, %r14, %r10
	li %r20, 2
	b 28f
27:
	rldicr %r9, %r19, 16, 47
	lis %r10, -2
	rldicr %r10, %r10, 32, 31
	or %r9, %r9, %r10
	li %r10, 32
	stdbrx %r9, %r14, %r10
	li %r20, 6
28:
26:
	rldicl %r10, %r19, 60, 4
	cmpldi %cr0, %r10, 0
	beq %cr0, 29f
	li %r10, 16
	b 210f
29:
	or %r10, %r19, %r19
210:
	li %r9, 16
	subf %r9, %r20, %r9
	subf %r11, %r9, %r10
	rldicl %r11, %r11, 1, 63
	cmpldi %cr0, %r11, 0
	beq %cr0, 211f
	or %r21, %r10, %r10
	b 212f
211:
	or %r21, %r9, %r9
212:
	add %r9, %r14, %r20
	addi %r9, %r9, 32
	or %r3, %r18, %r18
	or %r4, %r21, %r21
213:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 213b
	add %r18, %r18, %r21
	subf %r19, %r21, %r19
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 0
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	li %r7, 1
	bl {vg_cmac_aes_update}
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 0
	addi %r8, %r14, 384
	or %r6, %r18, %r18
	rldicl %r7, %r19, 60, 4
	bl {vg_cmac_aes_update}
	li %r9, 15
	and %r21, %r19, %r9
	cmpldi %cr0, %r21, 0
	beq %cr0, 214f
	li %r0, 0
	std %r0, 32(%r14)
	std %r0, 40(%r14)
	rldicl %r10, %r19, 60, 4
	rldicr %r10, %r10, 4, 59
	add %r3, %r18, %r10
	addi %r9, %r14, 32
	or %r4, %r21, %r21
216:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 216b
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 0
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	li %r7, 1
	bl {vg_cmac_aes_update}
	b 215f
214:
215:
	b 24f
23:
24:
	or %r18, %r22, %r22
	or %r19, %r23, %r23
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 0
	addi %r8, %r14, 384
	or %r6, %r18, %r18
	rldicl %r7, %r19, 60, 4
	bl {vg_cmac_aes_update}
	li %r9, 15
	and %r21, %r19, %r9
	cmpldi %cr0, %r21, 0
	beq %cr0, 217f
	li %r0, 0
	std %r0, 32(%r14)
	std %r0, 40(%r14)
	rldicl %r10, %r19, 60, 4
	rldicr %r10, %r10, 4, 59
	add %r3, %r18, %r10
	addi %r9, %r14, 32
	or %r4, %r21, %r21
219:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 219b
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 0
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	li %r7, 1
	bl {vg_cmac_aes_update}
	b 218f
217:
218:
	li %r9, 0
	ld %r10, 48(%r14)
	std %r10, 64(%r14)
	li %r11, 56
	ldbrx %r12, %r14, %r11
	or %r12, %r12, %r9
	li %r11, 72
	stdbrx %r12, %r14, %r11
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 64
	addi %r8, %r14, 384
	addi %r6, %r14, 0
	li %r7, 1
	bl {vg_aes_ctr32}
	or %r18, %r22, %r22
	rldicl %r19, %r23, 60, 4
	li %r20, 1
	cmpldi %cr0, %r19, 0
	beq %cr0, 220f
222:
	rldicr %r9, %r20, 32, 31
	rldicl %r9, %r9, 32, 32
	li %r10, 1
	rldicr %r10, %r10, 32, 31
	subf %r10, %r9, %r10
	subf %r11, %r10, %r19
	rldicl %r11, %r11, 1, 63
	cmpldi %cr0, %r11, 0
	beq %cr0, 223f
	or %r21, %r19, %r19
	b 224f
223:
	or %r21, %r10, %r10
224:
	or %r9, %r20, %r20
	ld %r10, 48(%r14)
	std %r10, 64(%r14)
	li %r11, 56
	ldbrx %r12, %r14, %r11
	or %r12, %r12, %r9
	li %r11, 72
	stdbrx %r12, %r14, %r11
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 64
	addi %r8, %r14, 384
	or %r6, %r18, %r18
	or %r7, %r21, %r21
	bl {vg_aes_ctr32}
	subf %r19, %r21, %r19
	add %r20, %r20, %r21
	rldicr %r9, %r21, 4, 59
	add %r18, %r18, %r9
	cmpldi %cr0, %r19, 0
	bne %cr0, 222b
	b 221f
220:
221:
	li %r9, 15
	and %r21, %r23, %r9
	cmpldi %cr0, %r21, 0
	beq %cr0, 225f
	or %r9, %r20, %r20
	ld %r10, 48(%r14)
	std %r10, 64(%r14)
	li %r11, 56
	ldbrx %r12, %r14, %r11
	or %r12, %r12, %r9
	li %r11, 72
	stdbrx %r12, %r14, %r11
	li %r0, 0
	std %r0, 80(%r14)
	std %r0, 88(%r14)
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 64
	addi %r8, %r14, 384
	addi %r6, %r14, 80
	li %r7, 1
	bl {vg_aes_ctr32}
	addi %r3, %r14, 80
	or %r9, %r18, %r18
	or %r4, %r21, %r21
227:
	lbz %r0, 0(%r3)
	lbz %r5, 0(%r9)
	xor %r0, %r0, %r5
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 227b
	b 226f
225:
226:
	ld %r9, 240(%r14)
	or %r3, %r14, %r14
	or %r4, %r15, %r15
228:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 228b
	ld %r0, 208(%r14)
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
	ld %r14, 128(%r14)
	addi %r1, %r1, 2688
	blr

vg_aes_ccm_open:
	stdu %r1, -2688(%r1)
	addi %r12, %r1, 0
	ld %r0, 2784(%r12)
	std %r0, 96(%r12)
	ld %r0, 2792(%r12)
	std %r0, 104(%r12)
	addi %r0, %r12, 120
	std %r0, 112(%r12)
	addi %r12, %r1, 0
	ld %r11, 112(%r12)
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
	std %r14, 128(%r11)
	std %r0, 208(%r11)
	or %r14, %r11, %r11
	ld %r15, 104(%r12)
	ld %r11, 96(%r12)
	or %r16, %r3, %r3
	or %r17, %r4, %r4
	std %r7, 216(%r14)
	std %r8, 224(%r14)
	std %r6, 232(%r14)
	std %r11, 240(%r14)
	or %r22, %r9, %r9
	or %r23, %r10, %r10
	li %r0, 0
	std %r0, 48(%r14)
	std %r0, 56(%r14)
	li %r9, 14
	subf %r9, %r6, %r9
	stb %r9, 48(%r14)
	or %r3, %r5, %r5
	addi %r9, %r14, 49
	or %r4, %r6, %r6
20:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 20b
	or %r18, %r22, %r22
	rldicl %r19, %r23, 60, 4
	li %r20, 1
	cmpldi %cr0, %r19, 0
	beq %cr0, 21f
23:
	rldicr %r9, %r20, 32, 31
	rldicl %r9, %r9, 32, 32
	li %r10, 1
	rldicr %r10, %r10, 32, 31
	subf %r10, %r9, %r10
	subf %r11, %r10, %r19
	rldicl %r11, %r11, 1, 63
	cmpldi %cr0, %r11, 0
	beq %cr0, 24f
	or %r21, %r19, %r19
	b 25f
24:
	or %r21, %r10, %r10
25:
	or %r9, %r20, %r20
	ld %r10, 48(%r14)
	std %r10, 64(%r14)
	li %r11, 56
	ldbrx %r12, %r14, %r11
	or %r12, %r12, %r9
	li %r11, 72
	stdbrx %r12, %r14, %r11
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 64
	addi %r8, %r14, 384
	or %r6, %r18, %r18
	or %r7, %r21, %r21
	bl {vg_aes_ctr32}
	subf %r19, %r21, %r19
	add %r20, %r20, %r21
	rldicr %r9, %r21, 4, 59
	add %r18, %r18, %r9
	cmpldi %cr0, %r19, 0
	bne %cr0, 23b
	b 22f
21:
22:
	li %r9, 15
	and %r21, %r23, %r9
	cmpldi %cr0, %r21, 0
	beq %cr0, 26f
	or %r9, %r20, %r20
	ld %r10, 48(%r14)
	std %r10, 64(%r14)
	li %r11, 56
	ldbrx %r12, %r14, %r11
	or %r12, %r12, %r9
	li %r11, 72
	stdbrx %r12, %r14, %r11
	li %r0, 0
	std %r0, 80(%r14)
	std %r0, 88(%r14)
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 64
	addi %r8, %r14, 384
	addi %r6, %r14, 80
	li %r7, 1
	bl {vg_aes_ctr32}
	addi %r3, %r14, 80
	or %r9, %r18, %r18
	or %r4, %r21, %r21
28:
	lbz %r0, 0(%r3)
	lbz %r5, 0(%r9)
	xor %r0, %r0, %r5
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 28b
	b 27f
26:
27:
	ld %r18, 216(%r14)
	ld %r19, 224(%r14)
	addi %r9, %r15, -2
	rldicr %r9, %r9, 2, 61
	ld %r10, 232(%r14)
	li %r11, 14
	subf %r11, %r10, %r11
	add %r9, %r9, %r11
	cmpldi %cr0, %r19, 0
	beq %cr0, 29f
	addi %r9, %r9, 64
	b 210f
29:
210:
	ld %r10, 48(%r14)
	ld %r11, 56(%r14)
	std %r10, 32(%r14)
	std %r11, 40(%r14)
	stb %r9, 32(%r14)
	li %r11, 40
	ldbrx %r12, %r14, %r11
	or %r12, %r12, %r23
	stdbrx %r12, %r14, %r11
	li %r0, 0
	std %r0, 96(%r14)
	std %r0, 104(%r14)
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 96
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	li %r7, 1
	bl {vg_cmac_aes_update}
	cmpldi %cr0, %r19, 0
	beq %cr0, 211f
	li %r0, 0
	std %r0, 32(%r14)
	std %r0, 40(%r14)
	rldicl %r9, %r19, 32, 32
	cmpldi %cr0, %r9, 0
	beq %cr0, 213f
	li %r9, 255
	stb %r9, 32(%r14)
	stb %r9, 33(%r14)
	li %r10, 34
	stdbrx %r19, %r14, %r10
	li %r20, 10
	b 214f
213:
	rldicl %r9, %r19, 56, 8
	addi %r9, %r9, -255
	rldicl %r9, %r9, 1, 63
	cmpldi %cr0, %r9, 0
	beq %cr0, 215f
	rldicr %r9, %r19, 48, 15
	li %r10, 32
	stdbrx %r9, %r14, %r10
	li %r20, 2
	b 216f
215:
	rldicr %r9, %r19, 16, 47
	lis %r10, -2
	rldicr %r10, %r10, 32, 31
	or %r9, %r9, %r10
	li %r10, 32
	stdbrx %r9, %r14, %r10
	li %r20, 6
216:
214:
	rldicl %r10, %r19, 60, 4
	cmpldi %cr0, %r10, 0
	beq %cr0, 217f
	li %r10, 16
	b 218f
217:
	or %r10, %r19, %r19
218:
	li %r9, 16
	subf %r9, %r20, %r9
	subf %r11, %r9, %r10
	rldicl %r11, %r11, 1, 63
	cmpldi %cr0, %r11, 0
	beq %cr0, 219f
	or %r21, %r10, %r10
	b 220f
219:
	or %r21, %r9, %r9
220:
	add %r9, %r14, %r20
	addi %r9, %r9, 32
	or %r3, %r18, %r18
	or %r4, %r21, %r21
221:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 221b
	add %r18, %r18, %r21
	subf %r19, %r21, %r19
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 96
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	li %r7, 1
	bl {vg_cmac_aes_update}
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 96
	addi %r8, %r14, 384
	or %r6, %r18, %r18
	rldicl %r7, %r19, 60, 4
	bl {vg_cmac_aes_update}
	li %r9, 15
	and %r21, %r19, %r9
	cmpldi %cr0, %r21, 0
	beq %cr0, 222f
	li %r0, 0
	std %r0, 32(%r14)
	std %r0, 40(%r14)
	rldicl %r10, %r19, 60, 4
	rldicr %r10, %r10, 4, 59
	add %r3, %r18, %r10
	addi %r9, %r14, 32
	or %r4, %r21, %r21
224:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 224b
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 96
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	li %r7, 1
	bl {vg_cmac_aes_update}
	b 223f
222:
223:
	b 212f
211:
212:
	or %r18, %r22, %r22
	or %r19, %r23, %r23
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 96
	addi %r8, %r14, 384
	or %r6, %r18, %r18
	rldicl %r7, %r19, 60, 4
	bl {vg_cmac_aes_update}
	li %r9, 15
	and %r21, %r19, %r9
	cmpldi %cr0, %r21, 0
	beq %cr0, 225f
	li %r0, 0
	std %r0, 32(%r14)
	std %r0, 40(%r14)
	rldicl %r10, %r19, 60, 4
	rldicr %r10, %r10, 4, 59
	add %r3, %r18, %r10
	addi %r9, %r14, 32
	or %r4, %r21, %r21
227:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 227b
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 96
	addi %r8, %r14, 384
	addi %r6, %r14, 32
	li %r7, 1
	bl {vg_cmac_aes_update}
	b 226f
225:
226:
	li %r9, 0
	ld %r10, 48(%r14)
	std %r10, 64(%r14)
	li %r11, 56
	ldbrx %r12, %r14, %r11
	or %r12, %r12, %r9
	li %r11, 72
	stdbrx %r12, %r14, %r11
	or %r3, %r16, %r16
	or %r4, %r17, %r17
	addi %r5, %r14, 64
	addi %r8, %r14, 384
	addi %r6, %r14, 96
	li %r7, 1
	bl {vg_aes_ctr32}
	ld %r18, 240(%r14)
	li %r0, 0
	std %r0, 256(%r14)
	std %r0, 264(%r14)
	li %r0, 0
	std %r0, 272(%r14)
	std %r0, 280(%r14)
	or %r3, %r18, %r18
	addi %r9, %r14, 272
	or %r4, %r15, %r15
228:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 228b
	addi %r3, %r14, 96
	addi %r9, %r14, 256
	or %r4, %r15, %r15
229:
	lbz %r0, 0(%r3)
	stb %r0, 0(%r9)
	addi %r3, %r3, 1
	addi %r9, %r9, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 229b
	ld %r5, 256(%r14)
	ld %r6, 272(%r14)
	xor %r5, %r5, %r6
	ld %r6, 264(%r14)
	ld %r7, 280(%r14)
	xor %r6, %r6, %r7
	or %r5, %r5, %r6
	li %r6, 0
	subf %r6, %r5, %r6
	or %r5, %r5, %r6
	rldicl %r5, %r5, 1, 63
	li %r21, 1
	subf %r21, %r5, %r21
	li %r9, 0
	subf %r9, %r21, %r9
	or %r3, %r22, %r22
	or %r4, %r23, %r23
	cmpldi %cr0, %r4, 0
	beq %cr0, 230f
232:
	lbz %r0, 0(%r3)
	and %r0, %r0, %r9
	stb %r0, 0(%r3)
	addi %r3, %r3, 1
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 232b
	b 231f
230:
231:
	or %r3, %r21, %r21
	ld %r0, 208(%r14)
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
	ld %r14, 128(%r14)
	addi %r1, %r1, 2688
	blr
