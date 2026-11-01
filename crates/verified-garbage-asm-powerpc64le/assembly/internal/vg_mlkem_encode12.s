// The functions of `src/internal/vg_mlkem_encode12.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_encode12:
	li %r5, 128
20:
	lwz %r6, 0(%r3)
	lwz %r7, 4(%r3)
	stb %r6, 0(%r4)
	rldicl %r6, %r6, 56, 8
	rldicr %r8, %r7, 4, 59
	add %r6, %r6, %r8
	stb %r6, 1(%r4)
	rldicl %r7, %r7, 60, 4
	stb %r7, 2(%r4)
	addi %r3, %r3, 8
	addi %r4, %r4, 3
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	blr
