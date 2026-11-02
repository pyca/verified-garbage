// The functions of `src/internal/vg_mldsa_make_hint.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_make_hint:
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
	lui a2, 2046
	addi a2, a2, 1
	addi t3, zero, 256
	addi t4, zero, 0
22:
	lwu a5, 0(a1)
	addi a5, a5, 127
	srli a5, a5, 7
	mul a5, a5, a7
	add a5, a5, t1
	srli a5, a5, 24
	sub a5, a5, t2
	srai a6, a5, 63
	and a6, a6, t2
	add a5, a5, a6
	sw a5, 0(a3)
	lwu a5, 0(a1)
	lwu a6, 0(a0)
	add a5, a5, a6
	sub a5, a5, a2
	srai a6, a5, 63
	and a6, a6, a2
	add a5, a5, a6
	addi a5, a5, 127
	srli a5, a5, 7
	mul a5, a5, a7
	add a5, a5, t1
	srli a5, a5, 24
	sub a5, a5, t2
	srai a6, a5, 63
	and a6, a6, t2
	add a5, a5, a6
	lwu a6, 0(a3)
	xor a5, a5, a6
	addi a5, a5, 63
	srli a5, a5, 6
	sw a5, 0(a3)
	add t4, t4, a5
	addi a0, a0, 4
	addi a1, a1, 4
	addi a3, a3, 4
	addi t3, t3, -1
	bnez t3, 22b
	addi a0, t4, 0
	j 21f
20:
	lui a7, 0
	addi a7, a7, 1025
	lui t1, 512
	addi t1, t1, 0
	addi t2, zero, 16
	lui a2, 2046
	addi a2, a2, 1
	addi t3, zero, 256
	addi t4, zero, 0
23:
	lwu a5, 0(a1)
	addi a5, a5, 127
	srli a5, a5, 7
	mul a5, a5, a7
	add a5, a5, t1
	srli a5, a5, 22
	sub a5, a5, t2
	srai a6, a5, 63
	and a6, a6, t2
	add a5, a5, a6
	sw a5, 0(a3)
	lwu a5, 0(a1)
	lwu a6, 0(a0)
	add a5, a5, a6
	sub a5, a5, a2
	srai a6, a5, 63
	and a6, a6, a2
	add a5, a5, a6
	addi a5, a5, 127
	srli a5, a5, 7
	mul a5, a5, a7
	add a5, a5, t1
	srli a5, a5, 22
	sub a5, a5, t2
	srai a6, a5, 63
	and a6, a6, t2
	add a5, a5, a6
	lwu a6, 0(a3)
	xor a5, a5, a6
	addi a5, a5, 63
	srli a5, a5, 6
	sw a5, 0(a3)
	add t4, t4, a5
	addi a0, a0, 4
	addi a1, a1, 4
	addi a3, a3, 4
	addi t3, t3, -1
	bnez t3, 23b
	addi a0, t4, 0
21:
	ret
	.option pop
