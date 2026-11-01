// The functions of `src/ct.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_ct_eq:
	.option push
	.option arch, +m, +c
	addi a4, zero, 0
	sub a7, a1, a3
	beqz a7, 20f
	addi a0, zero, 0
	j 21f
20:
	addi a5, zero, 0
	beqz a1, 22f
24:
	add t0, a0, a5
	lbu t1, 0(t0)
	add t0, a2, a5
	lbu t2, 0(t0)
	xor t1, t1, t2
	or a4, a4, t1
	addi a5, a5, 1
	sub a7, a5, a1
	bnez a7, 24b
	j 23f
22:
23:
	addi a4, a4, -1
	srli a0, a4, 63
21:
	ret
	.option pop
