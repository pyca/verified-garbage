// The functions of `src/mlkem768.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem768_keygen:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r12, %r1, 40
	std %r31, 0(%r12)
	or %r31, %r6, %r6
	bl {vg_mlkem768_keygen_body}
	or %r11, %r3, %r3
	or %r3, %r31, %r31
	li %r4, 0
	oris %r4, %r4, 0
	ori %r4, %r4, 0
	or %r31, %r11, %r11
	bl {vg_zeroize}
	or %r3, %r31, %r31
	addi %r12, %r1, 40
	ld %r31, 0(%r12)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_mlkem768_encaps:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r12, %r1, 40
	std %r31, 0(%r12)
	or %r31, %r7, %r7
	bl {vg_mlkem768_encaps_body}
	or %r11, %r3, %r3
	or %r3, %r31, %r31
	li %r4, 0
	oris %r4, %r4, 0
	ori %r4, %r4, 0
	or %r31, %r11, %r11
	bl {vg_zeroize}
	or %r3, %r31, %r31
	addi %r12, %r1, 40
	ld %r31, 0(%r12)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_mlkem768_encaps_h:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r12, %r1, 40
	std %r31, 0(%r12)
	or %r31, %r8, %r8
	bl {vg_mlkem768_encaps_h_body}
	or %r11, %r3, %r3
	or %r3, %r31, %r31
	li %r4, 0
	oris %r4, %r4, 0
	ori %r4, %r4, 0
	or %r31, %r11, %r11
	bl {vg_zeroize}
	or %r3, %r31, %r31
	addi %r12, %r1, 40
	ld %r31, 0(%r12)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_mlkem768_decaps:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r12, %r1, 40
	std %r31, 0(%r12)
	or %r31, %r6, %r6
	bl {vg_mlkem768_decaps_body}
	or %r11, %r3, %r3
	or %r3, %r31, %r31
	li %r4, 0
	oris %r4, %r4, 0
	ori %r4, %r4, 0
	or %r31, %r11, %r11
	bl {vg_zeroize}
	or %r3, %r31, %r31
	addi %r12, %r1, 40
	ld %r31, 0(%r12)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_mlkem768_check_ek:
	li %r4, 384
	li %r5, 0
20:
	lbz %r6, 1(%r3)
	rldicr %r6, %r6, 60, 3
	rldicl %r6, %r6, 12, 52
	lbz %r7, 0(%r3)
	add %r6, %r6, %r7
	li %r7, 3328
	subf %r7, %r6, %r7
	rldicl %r7, %r7, 1, 63
	add %r5, %r5, %r7
	lbz %r6, 1(%r3)
	rldicl %r6, %r6, 60, 4
	lbz %r7, 2(%r3)
	rldicr %r7, %r7, 4, 59
	add %r6, %r6, %r7
	li %r7, 3328
	subf %r7, %r6, %r7
	rldicl %r7, %r7, 1, 63
	add %r5, %r5, %r7
	addi %r3, %r3, 3
	addi %r4, %r4, -1
	cmpldi %cr0, %r4, 0
	bne %cr0, 20b
	li %r6, 0
	subf %r6, %r5, %r6
	rldicl %r6, %r6, 1, 63
	li %r3, 1
	subf %r3, %r6, %r3
	blr
