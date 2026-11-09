// The functions of `src/internal/vg_rsa_pkcs1_encrypt_precomputed.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rsa_pkcs1_encrypt_precomputed:
	stdu %r1, -2224(%r1)
	addi %r12, %r1, 0
	std %r28, 112(%r12)
	std %r29, 120(%r12)
	std %r30, 128(%r12)
	std %r31, 136(%r12)
	mflr %r0
	std %r0, 144(%r12)
	or %r28, %r3, %r3
	or %r29, %r6, %r6
	or %r30, %r7, %r7
	or %r31, %r8, %r8
	li %r0, 0
	stb %r0, 168(%r12)
	li %r0, 2
	stb %r0, 169(%r12)
	ld %r4, 2320(%r12)
	addi %r11, %r12, 170
	li %r5, 0
	ld %r12, 2328(%r12)
20:
	lbz %r3, 0(%r4)
	stb %r3, 0(%r11)
	addi %r0, %r3, -1
	rldicl %r0, %r0, 1, 63
	or %r5, %r5, %r0
	addi %r4, %r4, 1
	addi %r11, %r11, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 20b
	li %r0, 0
	stb %r0, 0(%r11)
	addi %r11, %r11, 1
	addi %r12, %r1, 0
	cmpldi %cr0, %r10, 0
	bne %cr0, 21f
	b 22f
21:
	or %r7, %r9, %r9
	or %r4, %r11, %r11
	or %r8, %r10, %r10
23:
	lbz %r0, 0(%r7)
	stb %r0, 0(%r4)
	addi %r7, %r7, 1
	addi %r4, %r4, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 23b
22:
	std %r5, 152(%r12)
	or %r3, %r28, %r28
	or %r4, %r29, %r29
	or %r7, %r30, %r30
	or %r8, %r31, %r31
	addi %r9, %r12, 168
	or %r10, %r29, %r29
	ld %r0, 2336(%r12)
	std %r0, 96(%r12)
	ld %r0, 2344(%r12)
	std %r0, 104(%r12)
	ld %r5, 2352(%r12)
	ld %r6, 2360(%r12)
	bl {vg_rsa_public_precomputed_checked}
	addi %r12, %r1, 0
	ld %r9, 152(%r12)
	addi %r9, %r9, -1
	and %r3, %r3, %r9
	or %r11, %r28, %r28
	or %r8, %r29, %r29
24:
	lbz %r10, 0(%r11)
	and %r10, %r10, %r9
	stb %r10, 0(%r11)
	addi %r11, %r11, 1
	addi %r8, %r8, -1
	cmpldi %cr0, %r8, 0
	bne %cr0, 24b
	addi %r12, %r1, 0
	addi %r4, %r12, 168
	or %r11, %r29, %r29
	li %r0, 0
25:
	stb %r0, 0(%r4)
	addi %r4, %r4, 1
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 25b
	addi %r12, %r1, 0
	ld %r0, 144(%r12)
	mtlr %r0
	ld %r28, 112(%r12)
	ld %r29, 120(%r12)
	ld %r30, 128(%r12)
	ld %r31, 136(%r12)
	addi %r1, %r1, 2224
	blr
