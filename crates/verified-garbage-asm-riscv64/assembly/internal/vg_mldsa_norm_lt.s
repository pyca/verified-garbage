// The functions of `src/internal/vg_mldsa_norm_lt.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa_norm_lt:
	.option push
	.option arch, +m, +c
	slli a1, a1, 32
	srli a1, a1, 32
	addi a6, zero, 1
	addi t1, zero, 256
	lui a2, 2046
	addi a2, a2, 1
20:
	lwu t0, 0(a0)
	sltu t2, t0, a1
	sub t3, a2, t0
	sltu t3, t3, a1
	or t2, t2, t3
	and a6, a6, t2
	addi a0, a0, 4
	addi t1, t1, -1
	bnez t1, 20b
	addi a0, a6, 0
	ret
	.option pop
