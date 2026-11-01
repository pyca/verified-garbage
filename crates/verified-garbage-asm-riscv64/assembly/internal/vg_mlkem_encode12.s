// The functions of `src/internal/vg_mlkem_encode12.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_encode12:
	.option push
	.option arch, +m, +c
	addi a2, zero, 128
20:
	lwu a3, 0(a0)
	lwu a4, 4(a0)
	sb a3, 0(a1)
	srli a3, a3, 8
	slli a5, a4, 4
	add a3, a3, a5
	sb a3, 1(a1)
	srli a4, a4, 4
	sb a4, 2(a1)
	addi a0, a0, 8
	addi a1, a1, 3
	addi a2, a2, -1
	bnez a2, 20b
	ret
	.option pop
