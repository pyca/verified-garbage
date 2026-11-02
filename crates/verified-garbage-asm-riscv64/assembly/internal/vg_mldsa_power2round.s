// The functions of `src/internal/vg_mldsa_power2round.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_power2round:
	.option push
	.option arch, +m, +c
	addi a3, zero, 256
	lui a4, 2046
	addi a4, a4, 1
	lui t2, 1
	addi t2, t2, -1
20:
	lwu a5, 0(a0)
	add a5, a5, t2
	srli a6, a5, 13
	sw a6, 0(a1)
	slli a7, a6, 13
	sub a5, a5, a7
	sub a5, a5, t2
	srai a6, a5, 63
	and a6, a6, a4
	add a5, a5, a6
	sw a5, 0(a2)
	addi a0, a0, 4
	addi a1, a1, 4
	addi a2, a2, 4
	addi a3, a3, -1
	bnez a3, 20b
	ret
	.option pop
