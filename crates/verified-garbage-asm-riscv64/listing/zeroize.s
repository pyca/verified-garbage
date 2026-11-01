// The functions of `src/zeroize.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_zeroize:
	.option push
	.option arch, +m, +c
	addi t0, zero, 0
	addi t1, zero, 0
	sub t1, t1, a0
	andi t1, t1, 7
	sltu t2, a1, t1
	bnez t2, 20f
	j 21f
20:
	addi t1, a1, 0
21:
	sub a1, a1, t1
	beqz t1, 22f
24:
	sb t0, 0(a0)
	addi a0, a0, 1
	addi t1, t1, -1
	bnez t1, 24b
	j 23f
22:
23:
	srli t1, a1, 3
	andi a1, a1, 7
	beqz t1, 25f
27:
	sd t0, 0(a0)
	addi a0, a0, 8
	addi t1, t1, -1
	bnez t1, 27b
	j 26f
25:
26:
	addi t1, a1, 0
	beqz t1, 28f
210:
	sb t0, 0(a0)
	addi a0, a0, 1
	addi t1, t1, -1
	bnez t1, 210b
	j 29f
28:
29:
	ret
	.option pop
