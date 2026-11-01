// The functions of `src/internal/vg_mldsa_unpack_t1.rs` of `verified-garbage-asm-powerpc64le`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_unpack_t1:
	addi %r10, %r3, 0
	addi %r11, %r4, 0
	li %r12, 64
20:
	li %r8, 0
	lbz %r9, 0(%r10)
	add %r8, %r8, %r9
	lbz %r9, 1(%r10)
	rldicr %r9, %r9, 8, 55
	add %r8, %r8, %r9
	rldicr %r9, %r8, 54, 9
	rldicl %r9, %r9, 10, 54
	rldicl %r8, %r8, 54, 10
	rldicr %r9, %r9, 13, 50
	stw %r9, 0(%r11)
	lbz %r9, 2(%r10)
	rldicr %r9, %r9, 6, 57
	add %r8, %r8, %r9
	rldicr %r9, %r8, 54, 9
	rldicl %r9, %r9, 10, 54
	rldicl %r8, %r8, 54, 10
	rldicr %r9, %r9, 13, 50
	stw %r9, 4(%r11)
	lbz %r9, 3(%r10)
	rldicr %r9, %r9, 4, 59
	add %r8, %r8, %r9
	rldicr %r9, %r8, 54, 9
	rldicl %r9, %r9, 10, 54
	rldicl %r8, %r8, 54, 10
	rldicr %r9, %r9, 13, 50
	stw %r9, 8(%r11)
	lbz %r9, 4(%r10)
	rldicr %r9, %r9, 2, 61
	add %r8, %r8, %r9
	rldicr %r9, %r8, 54, 9
	rldicl %r9, %r9, 10, 54
	rldicl %r8, %r8, 54, 10
	rldicr %r9, %r9, 13, 50
	stw %r9, 12(%r11)
	addi %r10, %r10, 5
	addi %r11, %r11, 16
	addi %r12, %r12, -1
	cmpldi %cr0, %r12, 0
	bne %cr0, 20b
	blr
