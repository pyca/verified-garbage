// The functions of `src/internal/vg_mlkem_cbd2.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_cbd2:
	.option push
	.option arch, +m, +c
	addi a2, zero, 128
	lui a5, 1
	addi a5, a5, -767
20:
	lbu a3, 0(a0)
	slli a3, a3, 62
	srli a3, a3, 62
	srli a6, a3, 1
	sub a3, a3, a6
	lbu a4, 0(a0)
	slli a4, a4, 60
	srli a4, a4, 62
	srli a6, a4, 1
	sub a4, a4, a6
	sub a3, a3, a4
	srai a4, a3, 63
	and a4, a4, a5
	add a3, a3, a4
	sw a3, 0(a1)
	lbu a3, 0(a0)
	slli a3, a3, 58
	srli a3, a3, 62
	srli a6, a3, 1
	sub a3, a3, a6
	lbu a4, 0(a0)
	slli a4, a4, 56
	srli a4, a4, 62
	srli a6, a4, 1
	sub a4, a4, a6
	sub a3, a3, a4
	srai a4, a3, 63
	and a4, a4, a5
	add a3, a3, a4
	sw a3, 4(a1)
	addi a0, a0, 1
	addi a1, a1, 8
	addi a2, a2, -1
	bnez a2, 20b
	ret
	.option pop
