// The functions of `src/aes_ecb.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_aes_ecb_encrypt:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r12, %r1, 40
	std %r31, 0(%r12)
	or %r31, %r7, %r7
	bl {vg_aes_encrypt_blocks}
	or %r11, %r3, %r3
	or %r3, %r31, %r31
	li %r4, 0
	oris %r4, %r4, 0
	ori %r4, %r4, 2048
	or %r31, %r11, %r11
	bl {vg_zeroize}
	or %r3, %r31, %r31
	addi %r12, %r1, 40
	ld %r31, 0(%r12)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr

vg_aes_ecb_decrypt:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	addi %r12, %r1, 40
	std %r31, 0(%r12)
	or %r31, %r7, %r7
	bl {vg_aes_decrypt_blocks}
	or %r11, %r3, %r3
	or %r3, %r31, %r31
	li %r4, 0
	oris %r4, %r4, 0
	ori %r4, %r4, 2048
	or %r31, %r11, %r11
	bl {vg_zeroize}
	or %r3, %r31, %r31
	addi %r12, %r1, 40
	ld %r31, 0(%r12)
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
