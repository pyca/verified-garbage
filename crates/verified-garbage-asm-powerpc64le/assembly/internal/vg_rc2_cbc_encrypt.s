// The functions of `src/internal/vg_rc2_cbc_encrypt.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_rc2_cbc_encrypt:
	mflr %r0
	std %r26, 256(%r7)
	std %r27, 264(%r7)
	std %r28, 272(%r7)
	std %r29, 280(%r7)
	std %r31, 296(%r7)
	std %r0, 304(%r7)
	std %r30, 288(%r7)
	addi %r26, %r3, 0
	addi %r27, %r4, 0
	addi %r28, %r5, 0
	addi %r29, %r6, 0
	addi %r30, %r7, 0
	cmpldi %cr0, %r29, 0
	beq %cr0, 20f
22:
	ld %r10, 0(%r28)
	ld %r11, 0(%r27)
	xor %r10, %r10, %r11
	std %r10, 0(%r28)
	addi %r3, %r26, 0
	addi %r4, %r28, 0
	addi %r5, %r30, 0
	bl {vg_rc2_encrypt_block}
	ld %r10, 0(%r28)
	std %r10, 0(%r27)
	addi %r28, %r28, 8
	addi %r29, %r29, -1
	cmpldi %cr0, %r29, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r26, 256(%r30)
	ld %r27, 264(%r30)
	ld %r28, 272(%r30)
	ld %r29, 280(%r30)
	ld %r31, 296(%r30)
	ld %r0, 304(%r30)
	ld %r30, 288(%r30)
	mtlr %r0
	blr
