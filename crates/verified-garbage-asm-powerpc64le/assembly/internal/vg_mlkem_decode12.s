// The functions of `src/internal/vg_mlkem_decode12.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_decode12:
	li %r5, 128
	li %r8, 3329
20:
	lbz %r6, 0(%r3)
	lbz %r7, 1(%r3)
	rldicr %r7, %r7, 60, 3
	rldicl %r7, %r7, 12, 52
	add %r6, %r6, %r7
	subf %r6, %r8, %r6
	rldicl %r7, %r6, 1, 63
	mulld %r7, %r7, %r8
	add %r6, %r6, %r7
	stw %r6, 0(%r4)
	lbz %r6, 1(%r3)
	rldicl %r6, %r6, 60, 4
	lbz %r7, 2(%r3)
	rldicr %r7, %r7, 4, 59
	add %r6, %r6, %r7
	subf %r6, %r8, %r6
	rldicl %r7, %r6, 1, 63
	mulld %r7, %r7, %r8
	add %r6, %r6, %r7
	stw %r6, 4(%r4)
	addi %r3, %r3, 3
	addi %r4, %r4, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	blr
