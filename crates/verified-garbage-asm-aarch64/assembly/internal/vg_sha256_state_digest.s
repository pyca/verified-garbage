// The functions of `src/internal/vg_sha256_state_digest.rs` of `verified-garbage-asm-aarch64`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha256_state_digest:
	add x10, x19, #0
	add x11, x21, #0
	add x19, x0, #0
	add x21, x1, #0
	ldr q0, [x19, #0]
	ldr q1, [x19, #16]
	rev32 v0.16b, v0.16b
	rev32 v1.16b, v1.16b
	str q0, [x21, #0]
	str q1, [x21, #16]
	add x19, x10, #0
	add x21, x11, #0
	ret
	.p2align 6
