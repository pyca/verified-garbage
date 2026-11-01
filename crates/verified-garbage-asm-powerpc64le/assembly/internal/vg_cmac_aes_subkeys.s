// The functions of `src/internal/vg_cmac_aes_subkeys.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_cmac_aes_subkeys:
	mflr %r0
	std %r0, 2080(%r6)
	std %r14, 2064(%r6)
	std %r15, 2072(%r6)
	or %r14, %r5, %r5
	or %r15, %r6, %r6
	li %r9, 0
	std %r9, 0(%r5)
	std %r9, 8(%r5)
	or %r5, %r14, %r14
	li %r6, 1
	or %r7, %r15, %r15
	bl {vg_aes_encrypt_blocks}
	li %r11, 0
	ldbrx %r9, %r14, %r11
	li %r11, 8
	ldbrx %r10, %r14, %r11
	rldicl %r11, %r9, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r10, 1, 63
	rldicr %r9, %r9, 1, 62
	or %r9, %r9, %r12
	rldicr %r10, %r10, 1, 62
	xor %r10, %r10, %r11
	li %r11, 0
	stdbrx %r9, %r14, %r11
	li %r11, 8
	stdbrx %r10, %r14, %r11
	li %r11, 0
	ldbrx %r9, %r14, %r11
	li %r11, 8
	ldbrx %r10, %r14, %r11
	rldicl %r11, %r9, 1, 63
	li %r12, 0
	subf %r11, %r11, %r12
	li %r12, 135
	and %r11, %r11, %r12
	rldicl %r12, %r10, 1, 63
	rldicr %r9, %r9, 1, 62
	or %r9, %r9, %r12
	rldicr %r10, %r10, 1, 62
	xor %r10, %r10, %r11
	li %r11, 16
	stdbrx %r9, %r14, %r11
	li %r11, 24
	stdbrx %r10, %r14, %r11
	ld %r0, 2080(%r15)
	ld %r14, 2064(%r15)
	ld %r15, 2072(%r15)
	mtlr %r0
	blr
