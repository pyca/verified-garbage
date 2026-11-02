// The functions of `src/internal/vg_mldsa_use_hint.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_use_hint:
	.option push
	.option arch, +m, +c
	lui a4, 64
	addi a4, a4, -256
	subw t0, a2, a4
	beqz t0, 20f
	lui a7, 3
	addi a7, a7, -1013
	lui t1, 2048
	addi t1, t1, 0
	addi t2, zero, 44
	lui a2, 47
	addi a2, a2, -2048
	addi t3, zero, 256
22:
	lwu a5, 0(a1)
	lwu a6, 0(a1)
	addi a6, a6, 127
	srli a6, a6, 7
	mul a6, a6, a7
	add a6, a6, t1
	srli a6, a6, 24
	mul t0, a6, a2
	sub t0, t0, a5
	srli t0, t0, 63
	slli t0, t0, 1
	lwu a5, 0(a0)
	addi a5, a5, -1
	srli a5, a5, 63
	add a6, a6, t0
	mul t0, t0, a5
	sub a6, a6, t0
	add a6, a6, a5
	addi a6, a6, -1
	srai a5, a6, 63
	and a5, a5, t2
	add a6, a6, a5
	sub a6, a6, t2
	srai a5, a6, 63
	and a5, a5, t2
	add a6, a6, a5
	sw a6, 0(a3)
	addi a0, a0, 4
	addi a1, a1, 4
	addi a3, a3, 4
	addi t3, t3, -1
	bnez t3, 22b
	j 21f
20:
	lui a7, 0
	addi a7, a7, 1025
	lui t1, 512
	addi t1, t1, 0
	addi t2, zero, 16
	lui a2, 128
	addi a2, a2, -512
	addi t3, zero, 256
23:
	lwu a5, 0(a1)
	lwu a6, 0(a1)
	addi a6, a6, 127
	srli a6, a6, 7
	mul a6, a6, a7
	add a6, a6, t1
	srli a6, a6, 22
	mul t0, a6, a2
	sub t0, t0, a5
	srli t0, t0, 63
	slli t0, t0, 1
	lwu a5, 0(a0)
	addi a5, a5, -1
	srli a5, a5, 63
	add a6, a6, t0
	mul t0, t0, a5
	sub a6, a6, t0
	add a6, a6, a5
	addi a6, a6, -1
	srai a5, a6, 63
	and a5, a5, t2
	add a6, a6, a5
	sub a6, a6, t2
	srai a5, a6, 63
	and a5, a5, t2
	add a6, a6, a5
	sw a6, 0(a3)
	addi a0, a0, 4
	addi a1, a1, 4
	addi a3, a3, 4
	addi t3, t3, -1
	bnez t3, 23b
21:
	ret
	.option pop
