// The functions of `src/internal/vg_mldsa_low_bits.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_low_bits:
	.option push
	.option arch, +m, +c
	lui a4, 64
	addi a4, a4, -256
	subw t0, a1, a4
	beqz t0, 20f
	lui a7, 3
	addi a7, a7, -1013
	lui t1, 2048
	addi t1, t1, 0
	addi t2, zero, 44
	lui a1, 47
	addi a1, a1, -2048
	lui a4, 2046
	addi a4, a4, 1
	addi a3, zero, 256
22:
	lwu a5, 0(a0)
	lwu t0, 0(a0)
	addi a5, a5, 127
	srli a5, a5, 7
	mul a5, a5, a7
	add a5, a5, t1
	srli a5, a5, 24
	sub a5, a5, t2
	srai a6, a5, 63
	and a6, a6, t2
	add a5, a5, a6
	mul a5, a5, a1
	sub t0, t0, a5
	srai a6, t0, 63
	and a6, a6, a4
	add t0, t0, a6
	sw t0, 0(a2)
	addi a0, a0, 4
	addi a2, a2, 4
	addi a3, a3, -1
	bnez a3, 22b
	j 21f
20:
	lui a7, 0
	addi a7, a7, 1025
	lui t1, 512
	addi t1, t1, 0
	addi t2, zero, 16
	lui a1, 128
	addi a1, a1, -512
	lui a4, 2046
	addi a4, a4, 1
	addi a3, zero, 256
23:
	lwu a5, 0(a0)
	lwu t0, 0(a0)
	addi a5, a5, 127
	srli a5, a5, 7
	mul a5, a5, a7
	add a5, a5, t1
	srli a5, a5, 22
	sub a5, a5, t2
	srai a6, a5, 63
	and a6, a6, t2
	add a5, a5, a6
	mul a5, a5, a1
	sub t0, t0, a5
	srai a6, t0, 63
	and a6, a6, a4
	add t0, t0, a6
	sw t0, 0(a2)
	addi a0, a0, 4
	addi a2, a2, 4
	addi a3, a3, -1
	bnez a3, 23b
21:
	ret
	.option pop
