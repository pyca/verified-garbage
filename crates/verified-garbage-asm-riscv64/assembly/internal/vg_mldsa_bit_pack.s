// The functions of `src/internal/vg_mldsa_bit_pack.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_bit_pack:
	.option push
	.option arch, +m, +c
	addi a7, a0, 0
	addi t1, a3, 0
	lui a4, 2046
	addi a4, a4, 1
	lui a6, 0
	addi a6, a6, 2
	subw a6, a2, a6
	beqz a6, 20f
	lui a6, 0
	addi a6, a6, 4
	subw a6, a2, a6
	beqz a6, 22f
	lui a6, 1
	addi a6, a6, 0
	subw a6, a2, a6
	beqz a6, 24f
	lui a6, 32
	addi a6, a6, 0
	subw a6, a2, a6
	beqz a6, 26f
	lui a1, 128
	addi a1, a1, 0
	addi t2, zero, 128
28:
	addi a5, zero, 0
	lwu a6, 0(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	add a5, a5, a6
	sb a5, 0(t1)
	srli a5, a5, 8
	sb a5, 1(t1)
	srli a5, a5, 8
	lwu a6, 4(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 4
	add a5, a5, a6
	sb a5, 2(t1)
	srli a5, a5, 8
	sb a5, 3(t1)
	srli a5, a5, 8
	sb a5, 4(t1)
	srli a5, a5, 8
	addi a7, a7, 8
	addi t1, t1, 5
	addi t2, t2, -1
	bnez t2, 28b
	j 27f
26:
	lui a1, 32
	addi a1, a1, 0
	addi t2, zero, 64
29:
	addi a5, zero, 0
	lwu a6, 0(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	add a5, a5, a6
	sb a5, 0(t1)
	srli a5, a5, 8
	sb a5, 1(t1)
	srli a5, a5, 8
	lwu a6, 4(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 2
	add a5, a5, a6
	sb a5, 2(t1)
	srli a5, a5, 8
	sb a5, 3(t1)
	srli a5, a5, 8
	lwu a6, 8(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 4
	add a5, a5, a6
	sb a5, 4(t1)
	srli a5, a5, 8
	sb a5, 5(t1)
	srli a5, a5, 8
	lwu a6, 12(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 6
	add a5, a5, a6
	sb a5, 6(t1)
	srli a5, a5, 8
	sb a5, 7(t1)
	srli a5, a5, 8
	sb a5, 8(t1)
	srli a5, a5, 8
	addi a7, a7, 16
	addi t1, t1, 9
	addi t2, t2, -1
	bnez t2, 29b
27:
	j 25f
24:
	lui a1, 1
	addi a1, a1, 0
	addi t2, zero, 32
210:
	addi a5, zero, 0
	lwu a6, 0(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	add a5, a5, a6
	sb a5, 0(t1)
	srli a5, a5, 8
	lwu a6, 4(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 5
	add a5, a5, a6
	sb a5, 1(t1)
	srli a5, a5, 8
	sb a5, 2(t1)
	srli a5, a5, 8
	lwu a6, 8(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 2
	add a5, a5, a6
	sb a5, 3(t1)
	srli a5, a5, 8
	lwu a6, 12(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 7
	add a5, a5, a6
	sb a5, 4(t1)
	srli a5, a5, 8
	sb a5, 5(t1)
	srli a5, a5, 8
	lwu a6, 16(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 4
	add a5, a5, a6
	sb a5, 6(t1)
	srli a5, a5, 8
	sb a5, 7(t1)
	srli a5, a5, 8
	lwu a6, 20(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 1
	add a5, a5, a6
	sb a5, 8(t1)
	srli a5, a5, 8
	lwu a6, 24(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 6
	add a5, a5, a6
	sb a5, 9(t1)
	srli a5, a5, 8
	sb a5, 10(t1)
	srli a5, a5, 8
	lwu a6, 28(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 3
	add a5, a5, a6
	sb a5, 11(t1)
	srli a5, a5, 8
	sb a5, 12(t1)
	srli a5, a5, 8
	addi a7, a7, 32
	addi t1, t1, 13
	addi t2, t2, -1
	bnez t2, 210b
25:
	j 23f
22:
	lui a1, 0
	addi a1, a1, 4
	addi t2, zero, 128
211:
	addi a5, zero, 0
	lwu a6, 0(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	add a5, a5, a6
	lwu a6, 4(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 4
	add a5, a5, a6
	sb a5, 0(t1)
	srli a5, a5, 8
	addi a7, a7, 8
	addi t1, t1, 1
	addi t2, t2, -1
	bnez t2, 211b
23:
	j 21f
20:
	lui a1, 0
	addi a1, a1, 2
	addi t2, zero, 32
212:
	addi a5, zero, 0
	lwu a6, 0(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	add a5, a5, a6
	lwu a6, 4(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 3
	add a5, a5, a6
	lwu a6, 8(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 6
	add a5, a5, a6
	sb a5, 0(t1)
	srli a5, a5, 8
	lwu a6, 12(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 1
	add a5, a5, a6
	lwu a6, 16(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 4
	add a5, a5, a6
	lwu a6, 20(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 7
	add a5, a5, a6
	sb a5, 1(t1)
	srli a5, a5, 8
	lwu a6, 24(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 2
	add a5, a5, a6
	lwu a6, 28(a7)
	sub a6, a1, a6
	srai t0, a6, 63
	and t0, t0, a4
	add a6, a6, t0
	slli a6, a6, 5
	add a5, a5, a6
	sb a5, 2(t1)
	srli a5, a5, 8
	addi a7, a7, 32
	addi t1, t1, 3
	addi t2, t2, -1
	bnez t2, 212b
21:
	ret
	.option pop
