// The functions of `src/internal/vg_hmac_sha224_init_any_scratch.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_hmac_sha224_init_any_scratch:
	rldicl %r12, %r6, 57, 7
	li %r11, 127
	and %r11, %r6, %r11
	addi %r11, %r11, 63
	rldicl %r11, %r11, 57, 7
	add %r12, %r12, %r11
	cmpldi %cr0, %r12, 0
	bne %cr0, 20f
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r20, 160(%r7)
	std %r21, 168(%r7)
	std %r22, 176(%r7)
	std %r23, 184(%r7)
	std %r24, 192(%r7)
	std %r25, 200(%r7)
	addi %r20, %r3, 0
	addi %r21, %r7, 0
	addi %r22, %r4, 0
	addi %r23, %r5, 0
	addi %r24, %r6, 0
	bl {vg_sha224_init}
	addi %r3, %r22, 0
	bl {vg_sha224_init}
	li %r12, 54
	li %r25, 0
	addi %r9, %r23, 0
	addi %r10, %r24, 0
	cmpldi %cr0, %r10, 0
	beq %cr0, 22f
24:
	lbz %r8, 0(%r9)
	xor %r8, %r8, %r12
	add %r11, %r22, %r25
	stb %r8, 32(%r11)
	addi %r9, %r9, 1
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 24b
	b 23f
22:
23:
	li %r10, 64
	subf %r10, %r25, %r10
	cmpldi %cr0, %r10, 0
	beq %cr0, 25f
27:
	add %r11, %r22, %r25
	stb %r12, 32(%r11)
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 27b
	b 26f
25:
26:
	addi %r3, %r20, 0
	li %r4, 0
	addi %r5, %r22, 32
	li %r6, 64
	addi %r7, %r21, 0
	bl {vg_sha256_update_scratch}
	li %r12, 92
	li %r25, 0
	addi %r9, %r23, 0
	addi %r10, %r24, 0
	cmpldi %cr0, %r10, 0
	beq %cr0, 28f
210:
	lbz %r8, 0(%r9)
	xor %r8, %r8, %r12
	add %r11, %r20, %r25
	stb %r8, 32(%r11)
	addi %r9, %r9, 1
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 210b
	b 29f
28:
29:
	li %r10, 64
	subf %r10, %r25, %r10
	cmpldi %cr0, %r10, 0
	beq %cr0, 211f
213:
	add %r11, %r20, %r25
	stb %r12, 32(%r11)
	addi %r25, %r25, 1
	addi %r10, %r10, -1
	cmpldi %cr0, %r10, 0
	bne %cr0, 213b
	b 212f
211:
212:
	addi %r3, %r22, 0
	li %r4, 0
	addi %r5, %r20, 32
	li %r6, 64
	addi %r7, %r21, 0
	bl {vg_sha256_update_scratch}
	ld %r20, 160(%r21)
	ld %r22, 176(%r21)
	ld %r23, 184(%r21)
	ld %r24, 192(%r21)
	ld %r25, 200(%r21)
	ld %r21, 168(%r21)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
21:
	blr
20:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	std %r20, 336(%r7)
	std %r21, 344(%r7)
	std %r22, 352(%r7)
	std %r23, 360(%r7)
	std %r24, 368(%r7)
	std %r25, 376(%r7)
	addi %r21, %r7, 0
	addi %r22, %r3, 0
	addi %r23, %r4, 0
	addi %r24, %r6, 0
	addi %r25, %r5, 0
	addi %r20, %r7, 208
	addi %r3, %r20, 0
	bl {vg_sha224_init}
	addi %r3, %r20, 0
	li %r4, 0
	addi %r5, %r25, 0
	addi %r6, %r24, 0
	addi %r7, %r21, 0
	bl {vg_sha256_update_scratch}
	addi %r3, %r20, 0
	addi %r4, %r24, 0
	addi %r5, %r21, 304
	addi %r6, %r21, 0
	bl {vg_sha256_finalize_scratch}
	addi %r3, %r22, 0
	addi %r4, %r23, 0
	addi %r5, %r21, 304
	li %r6, 28
	addi %r7, %r21, 0
	ld %r20, 336(%r21)
	ld %r22, 352(%r21)
	ld %r23, 360(%r21)
	ld %r24, 368(%r21)
	ld %r25, 376(%r21)
	ld %r21, 344(%r21)
	bl {vg_hmac_sha224_init_scratch}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	b 21b
