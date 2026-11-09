// The functions of `src/internal/vg_blowfish_modes_prepare.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_blowfish_modes_prepare:
	.option push
	.option arch, +m, +c
	addi t0, s4, 56
	addi t2, a0, 0
	addi t4, zero, 1042
	slli t4, t4, 2
20:
	lbu t1, 0(t2)
	sb t1, 0(t0)
	addi t2, t2, 1
	addi t0, t0, 1
	addi t4, t4, -1
	bnez t4, 20b
	ret
	.option pop
