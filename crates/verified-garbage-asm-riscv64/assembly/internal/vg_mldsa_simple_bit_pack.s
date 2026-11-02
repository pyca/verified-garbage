// The functions of `src/internal/vg_mldsa_simple_bit_pack.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_simple_bit_pack:
	.option push
	.option arch, +m, +c
	addi a7, a0, 0
	addi t1, a2, 0
	lui a6, 0
	addi a6, a6, 15
	subw a6, a1, a6
	beqz a6, 20f
	lui a6, 0
	addi a6, a6, 43
	subw a6, a1, a6
	beqz a6, 22f
	addi t2, zero, 64
24:
	addi a5, zero, 0
	lwu a6, 0(a7)
	add a5, a5, a6
	sb a5, 0(t1)
	srli a5, a5, 8
	lwu a6, 4(a7)
	slli a6, a6, 2
	add a5, a5, a6
	sb a5, 1(t1)
	srli a5, a5, 8
	lwu a6, 8(a7)
	slli a6, a6, 4
	add a5, a5, a6
	sb a5, 2(t1)
	srli a5, a5, 8
	lwu a6, 12(a7)
	slli a6, a6, 6
	add a5, a5, a6
	sb a5, 3(t1)
	srli a5, a5, 8
	sb a5, 4(t1)
	srli a5, a5, 8
	addi a7, a7, 16
	addi t1, t1, 5
	addi t2, t2, -1
	bnez t2, 24b
	j 23f
22:
	addi t2, zero, 64
25:
	addi a5, zero, 0
	lwu a6, 0(a7)
	add a5, a5, a6
	lwu a6, 4(a7)
	slli a6, a6, 6
	add a5, a5, a6
	sb a5, 0(t1)
	srli a5, a5, 8
	lwu a6, 8(a7)
	slli a6, a6, 4
	add a5, a5, a6
	sb a5, 1(t1)
	srli a5, a5, 8
	lwu a6, 12(a7)
	slli a6, a6, 2
	add a5, a5, a6
	sb a5, 2(t1)
	srli a5, a5, 8
	addi a7, a7, 16
	addi t1, t1, 3
	addi t2, t2, -1
	bnez t2, 25b
23:
	j 21f
20:
	addi t2, zero, 128
26:
	addi a5, zero, 0
	lwu a6, 0(a7)
	add a5, a5, a6
	lwu a6, 4(a7)
	slli a6, a6, 4
	add a5, a5, a6
	sb a5, 0(t1)
	srli a5, a5, 8
	addi a7, a7, 8
	addi t1, t1, 1
	addi t2, t2, -1
	bnez t2, 26b
21:
	ret
	.option pop
