// The functions of `src/aes_cbc.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_cbc_encrypt:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r12, %r1, 40
	std %r31, 0(%r12)
	or %r31, %r8, %r8
	bl {vg_aes_cbc_encrypt_unwiped}
	or %r11, %r3, %r3
	or %r3, %r31, %r31
	li %r4, 0
	oris %r4, %r4, 0
	ori %r4, %r4, 2176
	or %r31, %r11, %r11
	bl {vg_zeroize}
	or %r3, %r31, %r31
	addi %r12, %r1, 40
	ld %r31, 0(%r12)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	li %r0, 0
	stdu %r1, -48(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	addi %r1, %r1, 48
	li %r3, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v19, %v19, %v19
	blr

vg_aes_cbc_decrypt:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r12, %r1, 40
	std %r31, 0(%r12)
	or %r31, %r8, %r8
	bl {vg_aes_cbc_decrypt_unwiped}
	or %r11, %r3, %r3
	or %r3, %r31, %r31
	li %r4, 0
	oris %r4, %r4, 0
	ori %r4, %r4, 2176
	or %r31, %r11, %r11
	bl {vg_zeroize}
	or %r3, %r31, %r31
	addi %r12, %r1, 40
	ld %r31, 0(%r12)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	li %r0, 0
	stdu %r1, -48(%r1)
	addi %r12, %r1, 32
	std %r0, 0(%r12)
	std %r0, 8(%r12)
	addi %r1, %r1, 48
	li %r3, 0
	li %r4, 0
	li %r5, 0
	li %r6, 0
	li %r7, 0
	li %r9, 0
	li %r10, 0
	li %r11, 0
	li %r12, 0
	vxor %v0, %v0, %v0
	vxor %v1, %v1, %v1
	vxor %v2, %v2, %v2
	vxor %v3, %v3, %v3
	vxor %v4, %v4, %v4
	vxor %v5, %v5, %v5
	vxor %v6, %v6, %v6
	vxor %v7, %v7, %v7
	vxor %v8, %v8, %v8
	vxor %v9, %v9, %v9
	vxor %v19, %v19, %v19
	blr
