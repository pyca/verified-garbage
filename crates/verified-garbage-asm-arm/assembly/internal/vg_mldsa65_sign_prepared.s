// The functions of `src/internal/vg_mldsa65_sign_prepared.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa65_sign_prepared:
	push {r4, lr}
	ldr r12, [sp, #8]
	mov r4, lr
	movw lr, #4032
	movt lr, #0
	add lr, r0, lr
	push {r12, lr}
	bl {vg_mldsa65_sign_with_cache}
	ldr r12, [sp], #8
	mov lr, r4
	ldr r4, [sp], #8
	bx lr
