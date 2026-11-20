// The functions of `src/internal/vg_cmac_aes_update.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_update:
	mflr %r0
	std %r0, 48(%r8)
	std %r14, 0(%r8)
	std %r15, 8(%r8)
	std %r16, 16(%r8)
	std %r17, 24(%r8)
	std %r18, 32(%r8)
	std %r19, 40(%r8)
	or %r14, %r3, %r3
	or %r15, %r4, %r4
	or %r16, %r5, %r5
	or %r17, %r6, %r6
	or %r18, %r7, %r7
	or %r19, %r8, %r8
	cmpldi %cr0, %r18, 0
	beq %cr0, 20f
22:
	ld %r9, 0(%r16)
	ld %r10, 0(%r17)
	xor %r9, %r9, %r10
	std %r9, 0(%r16)
	ld %r9, 8(%r16)
	ld %r10, 8(%r17)
	xor %r9, %r9, %r10
	std %r9, 8(%r16)
	or %r3, %r14, %r14
	or %r4, %r15, %r15
	or %r5, %r16, %r16
	li %r6, 1
	bl {vg_aes_encrypt_blocks}
	addi %r17, %r17, 16
	addi %r18, %r18, -1
	cmpldi %cr0, %r18, 0
	bne %cr0, 22b
	b 21f
20:
21:
	ld %r0, 48(%r19)
	ld %r14, 0(%r19)
	ld %r15, 8(%r19)
	ld %r16, 16(%r19)
	ld %r17, 24(%r19)
	ld %r18, 32(%r19)
	ld %r19, 40(%r19)
	mtlr %r0
	blr
