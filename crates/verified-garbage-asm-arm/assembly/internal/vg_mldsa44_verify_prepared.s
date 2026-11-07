// The functions of `src/internal/vg_mldsa44_verify_prepared.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_mldsa44_verify_prepared:
	push {r4, lr}
	mov r4, lr
	movw r12, #1312
	movt r12, #0
	add r12, r0, r12
	push {r12, lr}
	bl {vg_mldsa44_verify_with_cache}
	ldr r12, [sp], #8
	mov lr, r4
	ldr r4, [sp], #8
	bx lr
