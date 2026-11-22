// The functions of `src/sm4.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sm4_expand_key:
	stdu %r1, -3264(%r1)
	addi %r5, %r1, 32
	mflr %r0
	std %r0, 3216(%r5)
	bl {vg_sm4_expand_key_core}
	ld %r0, 3216(%r5)
	mtlr %r0
	addi %r12, %r1, 32
	li %r0, 0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	addi %r1, %r1, 3264
	li %r0, 0
	li %r4, 0
	li %r5, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	blr

vg_sm4_ecb_encrypt:
	stdu %r1, -3280(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 3232(%r6)
	std %r30, 3216(%r6)
	std %r31, 3224(%r6)
	or %r7, %r6, %r6
	or %r31, %r4, %r4
	or %r30, %r5, %r5
	li %r4, 0
	or %r5, %r7, %r7
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r5, %r30, %r30
	or %r8, %r7, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
22:
	rldicl %r9, %r5, 60, 4
	cmpldi %cr0, %r9, 0
	bne %cr0, 23f
	or %r12, %r5, %r5
	b 24f
23:
	li %r12, 16
24:
	or %r6, %r31, %r31
	addi %r10, %r8, 768
	or %r3, %r12, %r12
25:
	ld %r9, 0(%r6)
	std %r9, 0(%r10)
	ld %r9, 8(%r6)
	std %r9, 8(%r10)
	addi %r6, %r6, 16
	addi %r10, %r10, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 25b
	or %r3, %r7, %r7
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r8, %r7, %r7
	rldicl %r9, %r5, 60, 4
	cmpldi %cr0, %r9, 0
	bne %cr0, 26f
	or %r12, %r5, %r5
	b 27f
26:
	li %r12, 16
27:
	addi %r6, %r8, 768
	or %r10, %r31, %r31
	or %r3, %r12, %r12
28:
	ld %r9, 0(%r6)
	std %r9, 0(%r10)
	ld %r9, 8(%r6)
	std %r9, 8(%r10)
	addi %r6, %r6, 16
	addi %r10, %r10, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 28b
	subf %r5, %r12, %r5
	addi %r31, %r31, 256
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r30, 3216(%r7)
	ld %r0, 3232(%r7)
	mtlr %r0
	ld %r31, 3224(%r7)
	addi %r12, %r1, 32
	li %r0, 0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	addi %r1, %r1, 3280
	li %r0, 0
	li %r3, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	blr

vg_sm4_ecb_decrypt:
	stdu %r1, -3280(%r1)
	addi %r6, %r1, 32
	mflr %r0
	std %r0, 3232(%r6)
	std %r30, 3216(%r6)
	std %r31, 3224(%r6)
	or %r7, %r6, %r6
	or %r31, %r4, %r4
	or %r30, %r5, %r5
	li %r4, 1
	or %r5, %r7, %r7
	li %r6, 402
	bl {vg_sm4_prepare_keys}
	or %r5, %r30, %r30
	or %r8, %r7, %r7
	cmpldi %cr0, %r5, 0
	beq %cr0, 20f
22:
	rldicl %r9, %r5, 60, 4
	cmpldi %cr0, %r9, 0
	bne %cr0, 23f
	or %r12, %r5, %r5
	b 24f
23:
	li %r12, 16
24:
	or %r6, %r31, %r31
	addi %r10, %r8, 768
	or %r3, %r12, %r12
25:
	ld %r9, 0(%r6)
	std %r9, 0(%r10)
	ld %r9, 8(%r6)
	std %r9, 8(%r10)
	addi %r6, %r6, 16
	addi %r10, %r10, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 25b
	or %r3, %r7, %r7
	li %r4, 402
	bl {vg_sm4_crypt_prepared}
	or %r8, %r7, %r7
	rldicl %r9, %r5, 60, 4
	cmpldi %cr0, %r9, 0
	bne %cr0, 26f
	or %r12, %r5, %r5
	b 27f
26:
	li %r12, 16
27:
	addi %r6, %r8, 768
	or %r10, %r31, %r31
	or %r3, %r12, %r12
28:
	ld %r9, 0(%r6)
	std %r9, 0(%r10)
	ld %r9, 8(%r6)
	std %r9, 8(%r10)
	addi %r6, %r6, 16
	addi %r10, %r10, 16
	addi %r3, %r3, -1
	cmpldi %cr0, %r3, 0
	bne %cr0, 28b
	subf %r5, %r12, %r5
	addi %r31, %r31, 256
	cmpldi %cr0, %r5, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r30, 3216(%r7)
	ld %r0, 3232(%r7)
	mtlr %r0
	ld %r31, 3224(%r7)
	addi %r12, %r1, 32
	li %r0, 0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	addi %r12, %r12, 128
	dcbz %r12, %r0
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	std %r0, 16(%r12)
	std %r0, 24(%r12)
	std %r0, 32(%r12)
	std %r0, 40(%r12)
	std %r0, 48(%r12)
	std %r0, 56(%r12)
	std %r0, 64(%r12)
	std %r0, 72(%r12)
	std %r0, 80(%r12)
	std %r0, 88(%r12)
	std %r0, 96(%r12)
	std %r0, 104(%r12)
	std %r0, 112(%r12)
	std %r0, 120(%r12)
	std %r0, 128(%r12)
	std %r0, 136(%r12)
	std %r0, 144(%r12)
	std %r0, 152(%r12)
	std %r0, 160(%r12)
	std %r0, 168(%r12)
	addi %r1, %r1, 3280
	li %r0, 0
	li %r3, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r8, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	blr
