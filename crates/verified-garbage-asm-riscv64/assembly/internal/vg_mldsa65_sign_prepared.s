// The functions of `src/internal/vg_mldsa65_sign_prepared.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_sign_prepared:
	.option push
	.option arch, +m, +c
	addi sp, sp, -16
	sd ra, 8(sp)
	lui a5, 1
	addi a5, a5, -64
	add a5, a0, a5
	lui a6, 4
	addi a6, a6, 1024
	call {vg_mldsa65_sign_with_cache}
	ld ra, 8(sp)
	addi sp, sp, 16
	ret
	.option pop
