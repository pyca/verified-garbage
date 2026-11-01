// The functions of `src/internal/vg_argon2_hprime.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_argon2_hprime:
	std %r27, 840(%r7)
	std %r28, 848(%r7)
	std %r29, 856(%r7)
	std %r30, 864(%r7)
	std %r31, 872(%r7)
	mflr %r0
	std %r0, 880(%r7)
	addi %r31, %r7, 0
	addi %r27, %r3, 0
	addi %r28, %r4, 0
	addi %r29, %r5, 0
	addi %r30, %r6, 0
	stw %r6, 832(%r31)
	addi %r4, %r30, 0
	addi %r10, %r4, -65
	rldicl %r10, %r10, 1, 63
	cmpldi %cr0, %r10, 0
	bne %cr0, 20f
	li %r4, 64
	b 21f
20:
21:
	addi %r3, %r31, 0
	addi %r5, %r31, 832
	li %r6, 0
	bl {vg_blake2b_init}
	li %r4, 0
	addi %r5, %r31, 832
	li %r6, 4
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	li %r4, 4
	addi %r5, %r27, 0
	addi %r6, %r28, 0
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	addi %r4, %r28, 4
	addi %r3, %r31, 0
	addi %r5, %r31, 768
	addi %r6, %r31, 192
	bl {vg_blake2b_finalize_scratch}
	addi %r10, %r30, -65
	rldicl %r10, %r10, 1, 63
	cmpldi %cr0, %r10, 0
	bne %cr0, 22f
	li %r9, 32
	addi %r5, %r31, 768
24:
	lbz %r6, 0(%r5)
	stb %r6, 0(%r29)
	addi %r5, %r5, 1
	addi %r29, %r29, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 24b
	addi %r30, %r30, -32
	addi %r10, %r30, -65
	rldicl %r10, %r10, 1, 63
	cmpldi %cr0, %r10, 0
	bne %cr0, 25f
27:
	li %r4, 64
	addi %r3, %r31, 0
	addi %r5, %r31, 832
	li %r6, 0
	bl {vg_blake2b_init}
	li %r4, 0
	addi %r5, %r31, 768
	li %r6, 64
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	li %r4, 64
	addi %r3, %r31, 0
	addi %r5, %r31, 768
	addi %r6, %r31, 192
	bl {vg_blake2b_finalize_scratch}
	li %r9, 32
	addi %r5, %r31, 768
28:
	lbz %r6, 0(%r5)
	stb %r6, 0(%r29)
	addi %r5, %r5, 1
	addi %r29, %r29, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 28b
	addi %r30, %r30, -32
	addi %r10, %r30, -65
	rldicl %r10, %r10, 1, 63
	cmpldi %cr0, %r10, 0
	beq %cr0, 27b
	b 26f
25:
26:
	addi %r4, %r30, 0
	addi %r3, %r31, 0
	addi %r5, %r31, 832
	li %r6, 0
	bl {vg_blake2b_init}
	li %r4, 0
	addi %r5, %r31, 768
	li %r6, 64
	addi %r3, %r31, 0
	addi %r7, %r31, 192
	bl {vg_blake2b_update_scratch}
	li %r4, 64
	addi %r3, %r31, 0
	addi %r5, %r31, 768
	addi %r6, %r31, 192
	bl {vg_blake2b_finalize_scratch}
	b 23f
22:
23:
	addi %r9, %r30, 0
	addi %r5, %r31, 768
29:
	lbz %r6, 0(%r5)
	stb %r6, 0(%r29)
	addi %r5, %r5, 1
	addi %r29, %r29, 1
	addi %r9, %r9, -1
	cmpldi %cr0, %r9, 0
	bne %cr0, 29b
	ld %r0, 880(%r31)
	mtlr %r0
	ld %r27, 840(%r31)
	ld %r28, 848(%r31)
	ld %r29, 856(%r31)
	ld %r30, 864(%r31)
	ld %r31, 872(%r31)
	blr
