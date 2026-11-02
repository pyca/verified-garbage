// The functions of `src/internal/vg_mldsa_unpack_t1.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_unpack_t1:
	.option push
	.option arch, +m, +c
	addi a7, a0, 0
	addi t1, a1, 0
	addi t2, zero, 64
20:
	addi a5, zero, 0
	lbu a6, 0(a7)
	add a5, a5, a6
	lbu a6, 1(a7)
	slli a6, a6, 8
	add a5, a5, a6
	slli a6, a5, 54
	srli a6, a6, 54
	srli a5, a5, 10
	slli a6, a6, 13
	sw a6, 0(t1)
	lbu a6, 2(a7)
	slli a6, a6, 6
	add a5, a5, a6
	slli a6, a5, 54
	srli a6, a6, 54
	srli a5, a5, 10
	slli a6, a6, 13
	sw a6, 4(t1)
	lbu a6, 3(a7)
	slli a6, a6, 4
	add a5, a5, a6
	slli a6, a5, 54
	srli a6, a6, 54
	srli a5, a5, 10
	slli a6, a6, 13
	sw a6, 8(t1)
	lbu a6, 4(a7)
	slli a6, a6, 2
	add a5, a5, a6
	slli a6, a5, 54
	srli a6, a6, 54
	srli a5, a5, 10
	slli a6, a6, 13
	sw a6, 12(t1)
	addi a7, a7, 5
	addi t1, t1, 16
	addi t2, t2, -1
	bnez t2, 20b
	ret
	.option pop
