// The functions of `src/internal/vg_x448.rs` of `verified-garbage-asm-arm`, as text: generated from
// Lean (`lean/VerifiedGarbage/TCB/Rust.lean`) with them, and not compiled.
// Each instruction the printer encodes is here as its text, and in
// `src/` as its machine code, which `lean/VerifiedGarbage/TCB/<ISA>/Encode.lean`
// gives.

vg_x448:
	push {r10, lr}
	movw r10, #:lower16:({vg_gf448_r16_mul}
	movt r10, #:upper16:({vg_gf448_r16_mul}
2:
	add r10, pc
3:
	bl {vg_x448_core}
	ldr lr, [sp, #4]
	ldr r10, [sp], #8
	bx lr
