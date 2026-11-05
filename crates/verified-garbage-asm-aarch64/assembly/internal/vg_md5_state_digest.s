// The functions of `src/internal/vg_md5_state_digest.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_md5_state_digest:
	add x10, x19, #0
	add x11, x21, #0
	add x19, x0, #0
	add x21, x1, #0
	ldr w9, [x19, #0]
	str w9, [x21, #0]
	ldr w9, [x19, #4]
	str w9, [x21, #4]
	ldr w9, [x19, #8]
	str w9, [x21, #8]
	ldr w9, [x19, #12]
	str w9, [x21, #12]
	add x19, x10, #0
	add x21, x11, #0
	ret
	.p2align 6
