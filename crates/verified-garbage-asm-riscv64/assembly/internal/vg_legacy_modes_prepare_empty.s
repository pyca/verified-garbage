// The functions of `src/internal/vg_legacy_modes_prepare_empty.rs` of `verified-garbage-asm-riscv64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_legacy_modes_prepare_empty:
	.option push
	.option arch, +m, +c
	ret
	.option pop
