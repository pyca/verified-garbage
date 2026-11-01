// The functions of `src/internal/vg_mlkem_decode12.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_decode12:
	.option push
	.option arch, +m, +c
	addi a2, zero, 128
	lui a5, 1
	addi a5, a5, -767
20:
	lbu a3, 0(a0)
	lbu a4, 1(a0)
	slli a4, a4, 60
	srli a4, a4, 52
	add a3, a3, a4
	sub a3, a3, a5
	srai a4, a3, 63
	and a4, a4, a5
	add a3, a3, a4
	sw a3, 0(a1)
	lbu a3, 1(a0)
	srli a3, a3, 4
	lbu a4, 2(a0)
	slli a4, a4, 4
	add a3, a3, a4
	sub a3, a3, a5
	srai a4, a3, 63
	and a4, a4, a5
	add a3, a3, a4
	sw a3, 4(a1)
	addi a0, a0, 3
	addi a1, a1, 8
	addi a2, a2, -1
	bnez a2, 20b
	ret
	.option pop
