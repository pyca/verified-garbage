// The functions of `src/internal/vg_poly1305_init_core.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_poly1305_init_core:
	ldr r2, [r1, #0]
	str r2, [r0, #24]
	ldr r2, [r1, #4]
	str r2, [r0, #28]
	ldr r2, [r1, #8]
	str r2, [r0, #32]
	ldr r2, [r1, #12]
	str r2, [r0, #36]
	ldr r2, [r1, #16]
	str r2, [r0, #40]
	ldr r2, [r1, #20]
	str r2, [r0, #44]
	ldr r2, [r1, #24]
	str r2, [r0, #48]
	ldr r2, [r1, #28]
	str r2, [r0, #52]
	mov r2, #0
	str r2, [r0, #0]
	str r2, [r0, #4]
	str r2, [r0, #8]
	str r2, [r0, #12]
	str r2, [r0, #16]
	str r2, [r0, #20]
	bx lr
