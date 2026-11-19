// The functions of `src/internal/vg_sha1_init_core.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_sha1_init_core:
	movw r12, #8961
	movt r12, #26437
	str r12, [r0, #0]
	movw r12, #43913
	movt r12, #61389
	str r12, [r0, #4]
	movw r12, #56574
	movt r12, #39098
	str r12, [r0, #8]
	movw r12, #21622
	movt r12, #4146
	str r12, [r0, #12]
	movw r12, #57840
	movt r12, #50130
	str r12, [r0, #16]
	bx lr
