// The functions of `src/internal/vg_mlkem_sub.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mlkem_sub:
	.option push
	.option arch, +m, +c
	addi a2, zero, 256
	lui a5, 1
	addi a5, a5, -767
20:
	lwu a3, 0(a0)
	lwu a4, 0(a1)
	sub a3, a3, a4
	srai a4, a3, 63
	and a4, a4, a5
	add a3, a3, a4
	sw a3, 0(a0)
	addi a0, a0, 4
	addi a1, a1, 4
	addi a2, a2, -1
	bnez a2, 20b
	ret
	.option pop
