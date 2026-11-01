// The functions of `src/internal/vg_mlkem_cbd2.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_cbd2:
	li %r5, 128
	li %r8, 3329
20:
	lbz %r6, 0(%r3)
	rldicr %r6, %r6, 62, 1
	rldicl %r6, %r6, 2, 62
	rldicl %r9, %r6, 63, 1
	subf %r6, %r9, %r6
	lbz %r7, 0(%r3)
	rldicr %r7, %r7, 60, 3
	rldicl %r7, %r7, 2, 62
	rldicl %r9, %r7, 63, 1
	subf %r7, %r9, %r7
	subf %r6, %r7, %r6
	rldicl %r7, %r6, 1, 63
	mulld %r7, %r7, %r8
	add %r6, %r6, %r7
	stw %r6, 0(%r4)
	lbz %r6, 0(%r3)
	rldicr %r6, %r6, 58, 5
	rldicl %r6, %r6, 2, 62
	rldicl %r9, %r6, 63, 1
	subf %r6, %r9, %r6
	lbz %r7, 0(%r3)
	rldicr %r7, %r7, 56, 7
	rldicl %r7, %r7, 2, 62
	rldicl %r9, %r7, 63, 1
	subf %r7, %r9, %r7
	subf %r6, %r7, %r6
	rldicl %r7, %r6, 1, 63
	mulld %r7, %r7, %r8
	add %r6, %r6, %r7
	stw %r6, 4(%r4)
	addi %r3, %r3, 1
	addi %r4, %r4, 8
	addi %r5, %r5, -1
	cmpldi %cr0, %r5, 0
	bne %cr0, 20b
	blr
