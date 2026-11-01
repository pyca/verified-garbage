// The functions of `src/internal/vg_keccak_pad_scratch.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_keccak_pad_scratch:
	mflr %r0
	stdu %r1, -48(%r1)
	std %r0, 32(%r1)
	add %r9, %r3, %r5
	lbz %r10, 0(%r9)
	xor %r10, %r10, %r6
	stb %r10, 0(%r9)
	add %r9, %r3, %r4
	addi %r9, %r9, -1
	lbz %r10, 0(%r9)
	li %r11, 128
	xor %r10, %r10, %r11
	stb %r10, 0(%r9)
	addi %r4, %r7, 0
	bl {vg_keccak_f1600}
	ld %r0, 32(%r1)
	addi %r1, %r1, 48
	mtlr %r0
	blr
