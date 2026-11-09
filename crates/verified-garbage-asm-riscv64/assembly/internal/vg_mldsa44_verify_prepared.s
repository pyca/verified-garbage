// The functions of `src/internal/vg_mldsa44_verify_prepared.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_verify_prepared:
	.option push
	.option arch, +m, +c
	addi sp, sp, -16
	sd ra, 8(sp)
	lui a4, 0
	addi a4, a4, 1312
	add a4, a0, a4
	lui a5, 1
	addi a5, a5, 0
	call {vg_mldsa44_verify_with_cache}
	ld ra, 8(sp)
	addi sp, sp, 16
	ret
	.option pop
