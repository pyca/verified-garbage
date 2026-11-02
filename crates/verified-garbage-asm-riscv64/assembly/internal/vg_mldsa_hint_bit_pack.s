// The functions of `src/internal/vg_mldsa_hint_bit_pack.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_hint_bit_pack:
	.option push
	.option arch, +m, +c
	slli a2, a2, 32
	srli a2, a2, 32
	sub a1, a4, a2
	addi a6, a4, 0
	addi t0, zero, 0
	addi a7, a3, 0
20:
	sb t0, 0(a7)
	addi a7, a7, 1
	addi a6, a6, -1
	bnez a6, 20b
	addi a6, a1, 0
	add a7, a3, a2
	addi t1, zero, 0
21:
	addi t2, zero, 0
22:
	lwu a5, 0(a0)
	beqz a5, 23f
	add a5, a3, t1
	sb t2, 0(a5)
	addi t1, t1, 1
	j 24f
23:
24:
	addi a0, a0, 4
	addi t2, t2, 1
	addi a5, t2, -256
	bnez a5, 22b
	sb t1, 0(a7)
	addi a7, a7, 1
	addi a6, a6, -1
	bnez a6, 21b
	ret
	.option pop
