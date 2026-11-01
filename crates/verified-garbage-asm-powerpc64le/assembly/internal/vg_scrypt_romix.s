// The functions of `src/internal/vg_scrypt_romix.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_scrypt_romix:
	std %r24, 128(%r7)
	std %r25, 136(%r7)
	std %r26, 144(%r7)
	std %r28, 152(%r7)
	std %r29, 160(%r7)
	std %r27, 176(%r7)
	mflr %r0
	std %r0, 168(%r7)
	addi %r24, %r3, 0
	addi %r25, %r5, 0
	addi %r27, %r7, 0
	rldicr %r26, %r4, 7, 56
	addi %r9, %r4, 0
	li %r10, 1
	add %r11, %r6, %r6
20:
	add %r9, %r9, %r9
	add %r10, %r10, %r10
	subf %r12, %r11, %r9
	cmpldi %cr0, %r12, 0
	bne %cr0, 20b
	rldicl %r10, %r10, 63, 1
	std %r10, 184(%r27)
	addi %r28, %r10, 0
	addi %r29, %r25, 0
21:
	addi %r9, %r24, 0
	addi %r10, %r29, 0
	rldicl %r11, %r26, 61, 3
22:
	ld %r12, 0(%r9)
	std %r12, 0(%r10)
	addi %r9, %r9, 8
	addi %r10, %r10, 8
	addi %r11, %r11, -1
	cmpldi %cr0, %r11, 0
	bne %cr0, 22b
	addi %r3, %r29, 0
	rldicl %r4, %r26, 57, 7
	addi %r5, %r24, 0
	addi %r6, %r4, 0
	addi %r7, %r27, 0
	bl {vg_scrypt_blockmix}
	add %r29, %r29, %r26
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 21b
	ld %r28, 184(%r27)
	addi %r29, %r28, -1
23:
	add %r9, %r24, %r26
	addi %r9, %r9, -64
	ld %r9, 0(%r9)
	and %r9, %r9, %r29
	mulld %r10, %r9, %r26
	add %r10, %r10, %r25
	addi %r9, %r24, 0
	addi %r11, %r27, 192
	rldicl %r12, %r26, 61, 3
24:
	ld %r6, 0(%r9)
	ld %r8, 0(%r10)
	xor %r6, %r6, %r8
	std %r6, 0(%r11)
	addi %r9, %r9, 8
	addi %r10, %r10, 8
	addi %r11, %r11, 8
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	addi %r3, %r27, 192
	rldicl %r4, %r26, 57, 7
	addi %r5, %r24, 0
	addi %r6, %r4, 0
	addi %r7, %r27, 0
	bl {vg_scrypt_blockmix}
	addi %r28, %r28, -1
	cmpldi %cr0, %r28, 0
	bne %cr0, 23b
	ld %r0, 168(%r27)
	mtlr %r0
	ld %r24, 128(%r27)
	ld %r25, 136(%r27)
	ld %r26, 144(%r27)
	ld %r28, 152(%r27)
	ld %r29, 160(%r27)
	ld %r27, 176(%r27)
	blr
