// The functions of `src/internal/vg_cmac_aes_finalize.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_finalize:
	mflr %r0
	std %r0, 2064(%r8)
	std %r14, 2072(%r8)
	addi %r9, %r7, -16
	cmpldi %cr0, %r9, 0
	beq %cr0, 20f
	li %r9, 0
	std %r9, 2048(%r8)
	std %r9, 2056(%r8)
	addi %r10, %r8, 2048
	or %r11, %r6, %r6
	or %r12, %r7, %r7
	cmpldi %cr0, %r7, 0
	beq %cr0, 22f
24:
	lbz %r9, 0(%r11)
	stb %r9, 0(%r10)
	addi %r11, %r11, 1
	addi %r10, %r10, 1
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 24b
	b 23f
22:
23:
	li %r9, 128
	stb %r9, 0(%r10)
	ld %r9, 2048(%r8)
	ld %r10, 256(%r3)
	xor %r9, %r9, %r10
	std %r9, 2048(%r8)
	ld %r9, 2056(%r8)
	ld %r10, 264(%r3)
	xor %r9, %r9, %r10
	std %r9, 2056(%r8)
	b 21f
20:
	ld %r9, 0(%r6)
	ld %r10, 240(%r3)
	xor %r9, %r9, %r10
	std %r9, 2048(%r8)
	ld %r9, 8(%r6)
	ld %r10, 248(%r3)
	xor %r9, %r9, %r10
	std %r9, 2056(%r8)
21:
	ld %r9, 0(%r5)
	ld %r10, 2048(%r8)
	xor %r9, %r9, %r10
	std %r9, 0(%r5)
	ld %r9, 8(%r5)
	ld %r10, 2056(%r8)
	xor %r9, %r9, %r10
	std %r9, 8(%r5)
	or %r14, %r8, %r8
	li %r6, 1
	or %r7, %r14, %r14
	bl {vg_aes_encrypt_blocks}
	ld %r0, 2064(%r14)
	ld %r14, 2072(%r14)
	mtlr %r0
	blr
