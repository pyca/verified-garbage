// The functions of `src/internal/vg_mldsa_multiply_ntt.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_multiply_ntt:
	.option push
	.option arch, +m, +c
	lui a5, 131200
	addi a5, a5, 448
	slli a5, a5, 12
	addi a5, a5, 1537
	lui a6, 2046
	addi a6, a6, 1
	addi t1, zero, 256
20:
	lwu t0, 0(a1)
	lwu t2, 0(a2)
	mul t0, t0, t2
	mulhu t2, t0, a5
	mul t2, t2, a6
	sub t0, t0, t2
	sub t0, t0, a6
	srai t2, t0, 63
	and t2, t2, a6
	add t0, t0, t2
	sw t0, 0(a0)
	addi a0, a0, 4
	addi a1, a1, 4
	addi a2, a2, 4
	addi t1, t1, -1
	bnez t1, 20b
	ret
	.option pop
